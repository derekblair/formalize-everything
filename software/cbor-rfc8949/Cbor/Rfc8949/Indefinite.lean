/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Duplicates

/-!
# Indefinite lengths and `deflateIndefinite` (§3.2.1–§3.2.4)

`deflateIndefinite` is a wire-level rewrite (ticket #34 binding amendment
I4): it parses the input, replaces every indefinite-length string by one
definite string of its concatenated chunks and every indefinite array or
map by a definite one with the same elements in the same order, each new
head in preferred serialization, and re-serializes. Everything else —
including non-preferred heads of definite items, map order, tags — is kept
byte for byte (`deflateIndefinite_of_definite`). Ill-formed input is
returned unchanged.

A definite head carries at most 2^64 - 1, so an aggregate is rewritten only
when its size fits; otherwise it stays indefinite (with its contents still
deflated). Hence:

* syntax preservation holds unconditionally, in three forms — the tree form
  `parseWellFormed_deflateIndefinite`, the ∃ / equivalence form
  `deflateIndefinite_exists_equiv`, and the erasure form
  `parseWellFormed_deflateIndefinite_toDefinite`;
* idempotence (`deflateIndefinite_idem`) and commutation with
  `encodeDeterministic ∘ normalise` (`deflateIndefinite_normalise`) hold
  unconditionally;
* the output is definite exactly under the size hypothesis of the twice
  amended ticket (comments 6460668308 and 6487507282): at every indefinite
  aggregate, the chunk payloads of a string total fewer than 2^64 bytes, an
  array has fewer than 2^64 elements and a map fewer than 2^64 pairs
  (`Item.IndefBounded`, `deflateIndefinite_definite`). Any input shorter
  than 2^64 bytes satisfies it (`indefBounded_of_length_lt`).

The hypothesis cannot be dropped: `Cbor.Rfc8949.Boundary` proves that the
two wires of the fidelity-gate findings — an indefinite array of 2^64 zeros,
and an indefinite byte string of two 2^63-byte chunks (which meets the
withdrawn chunk-count bound) — have no definite encoding of an equivalent
item at all.
-/

namespace Cbor.Rfc8949

namespace Item

mutual
/-- The size hypothesis of ticket #34 deliverable 2 as twice amended, at every
indefinite aggregate: total chunk payload bytes of a string, elements of an
array, pairs of a map, each below 2^64. -/
def IndefBounded : Item → Prop
  | .bytesIndef cs => cs.flatten.length < 2 ^ 64
  | .textIndef cs => cs.flatten.length < 2 ^ 64
  | .array xs => IndefBoundedList xs
  | .arrayIndef xs => xs.length < 2 ^ 64 ∧ IndefBoundedList xs
  | .map kvs => IndefBoundedPairs kvs
  | .mapIndef kvs => kvs.length < 2 ^ 64 ∧ IndefBoundedPairs kvs
  | .tag _ x => IndefBounded x
  | _ => True
def IndefBoundedList : List Item → Prop
  | [] => True
  | x :: xs => IndefBounded x ∧ IndefBoundedList xs
def IndefBoundedPairs : List (Item × Item) → Prop
  | [] => True
  | (k, v) :: kvs => IndefBounded k ∧ IndefBounded v ∧ IndefBoundedPairs kvs
end

mutual
/-- No indefinite-length item anywhere. -/
def Definite : Item → Prop
  | .bytesIndef _ | .textIndef _ | .arrayIndef _ | .mapIndef _ => False
  | .array xs => DefiniteList xs
  | .map kvs => DefinitePairs kvs
  | .tag _ x => Definite x
  | _ => True
def DefiniteList : List Item → Prop
  | [] => True
  | x :: xs => Definite x ∧ DefiniteList xs
def DefinitePairs : List (Item × Item) → Prop
  | [] => True
  | (k, v) :: kvs => Definite k ∧ Definite v ∧ DefinitePairs kvs
end

mutual
/-- Item-level deflation: indefinite aggregates whose size fits a definite
head become definite; nothing is reordered or reinterpreted. -/
def deflate : Item → Item
  | .bytesIndef cs => if cs.flatten.length < 2 ^ 64 then .bytes cs.flatten else .bytesIndef cs
  | .textIndef cs => if cs.flatten.length < 2 ^ 64 then .text cs.flatten else .textIndef cs
  | .array xs => .array (deflateList xs)
  | .arrayIndef xs =>
    if xs.length < 2 ^ 64 then .array (deflateList xs) else .arrayIndef (deflateList xs)
  | .map kvs => .map (deflatePairs kvs)
  | .mapIndef kvs =>
    if kvs.length < 2 ^ 64 then .map (deflatePairs kvs) else .mapIndef (deflatePairs kvs)
  | .tag t x => .tag t (deflate x)
  | .uint n => .uint n
  | .nint n => .nint n
  | .bytes p => .bytes p
  | .text p => .text p
  | .simple v => .simple v
def deflateList : List Item → List Item
  | [] => []
  | x :: xs => deflate x :: deflateList xs
def deflatePairs : List (Item × Item) → List (Item × Item)
  | [] => []
  | (k, v) :: kvs => (deflate k, deflate v) :: deflatePairs kvs
end

mutual
/-- Erase the definite/indefinite serialization choice (§2: not visible in
the data model): every indefinite aggregate becomes definite, regardless of
size. -/
def toDefinite : Item → Item
  | .bytesIndef cs => .bytes cs.flatten
  | .textIndef cs => .text cs.flatten
  | .array xs => .array (toDefiniteList xs)
  | .arrayIndef xs => .array (toDefiniteList xs)
  | .map kvs => .map (toDefinitePairs kvs)
  | .mapIndef kvs => .map (toDefinitePairs kvs)
  | .tag t x => .tag t (toDefinite x)
  | .uint n => .uint n
  | .nint n => .nint n
  | .bytes p => .bytes p
  | .text p => .text p
  | .simple v => .simple v
def toDefiniteList : List Item → List Item
  | [] => []
  | x :: xs => toDefinite x :: toDefiniteList xs
def toDefinitePairs : List (Item × Item) → List (Item × Item)
  | [] => []
  | (k, v) :: kvs => (toDefinite k, toDefinite v) :: toDefinitePairs kvs
end

end Item

namespace RawItem

mutual
/-- Wire-level deflation: like `Item.deflate`, keeping the width of every
existing definite head and giving each new definite head its preferred
width (§4.1). -/
def deflate : RawItem → RawItem
  | .bytesIndef cs =>
    if (cs.map Prod.snd).flatten.length < 2 ^ 64 then
      .bytes (Width.preferred (cs.map Prod.snd).flatten.length) (cs.map Prod.snd).flatten
    else .bytesIndef cs
  | .textIndef cs =>
    if (cs.map Prod.snd).flatten.length < 2 ^ 64 then
      .text (Width.preferred (cs.map Prod.snd).flatten.length) (cs.map Prod.snd).flatten
    else .textIndef cs
  | .array w xs => .array w (deflateList xs)
  | .arrayIndef xs =>
    if xs.length < 2 ^ 64 then .array (Width.preferred xs.length) (deflateList xs)
    else .arrayIndef (deflateList xs)
  | .map w kvs => .map w (deflatePairs kvs)
  | .mapIndef kvs =>
    if kvs.length < 2 ^ 64 then .map (Width.preferred kvs.length) (deflatePairs kvs)
    else .mapIndef (deflatePairs kvs)
  | .tag w t x => .tag w t (deflate x)
  | .uint w n => .uint w n
  | .nint w n => .nint w n
  | .bytes w p => .bytes w p
  | .text w p => .text w p
  | .simple v => .simple v
def deflateList : List RawItem → List RawItem
  | [] => []
  | x :: xs => deflate x :: deflateList xs
def deflatePairs : List (RawItem × RawItem) → List (RawItem × RawItem)
  | [] => []
  | (k, v) :: kvs => (deflate k, deflate v) :: deflatePairs kvs
end

end RawItem

/-- **Wire-level deflation (I4).** Rewrite every indefinite-length item of a
well-formed input to a definite one with a preferred head, keeping all other
bytes; inputs that are not one well-formed item are returned unchanged. -/
def deflateIndefinite (bs : List UInt8) : List UInt8 :=
  match parseRaw bs with
  | some r => r.deflate.encode
  | none => bs

/-! ## List views -/

namespace Item

theorem deflateList_eq (xs : List Item) : deflateList xs = xs.map deflate := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [deflateList, ih]

theorem deflatePairs_eq (kvs : List (Item × Item)) :
    deflatePairs kvs = kvs.map fun kv => (deflate kv.1, deflate kv.2) := by
  induction kvs with
  | nil => rfl
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [deflatePairs, ih]

theorem toDefiniteList_eq (xs : List Item) : toDefiniteList xs = xs.map toDefinite := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [toDefiniteList, ih]

theorem toDefinitePairs_eq (kvs : List (Item × Item)) :
    toDefinitePairs kvs = kvs.map fun kv => (toDefinite kv.1, toDefinite kv.2) := by
  induction kvs with
  | nil => rfl
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [toDefinitePairs, ih]

theorem IndefBoundedList_iff (xs : List Item) :
    IndefBoundedList xs ↔ ∀ x ∈ xs, IndefBounded x := by
  induction xs with
  | nil => simp [IndefBoundedList]
  | cons x xs ih => simp [IndefBoundedList, ih]

theorem IndefBoundedPairs_iff (kvs : List (Item × Item)) :
    IndefBoundedPairs kvs ↔ ∀ kv ∈ kvs, IndefBounded kv.1 ∧ IndefBounded kv.2 := by
  induction kvs with
  | nil => simp [IndefBoundedPairs]
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [IndefBoundedPairs, ih, and_assoc]

theorem DefiniteList_iff (xs : List Item) : DefiniteList xs ↔ ∀ x ∈ xs, Definite x := by
  induction xs with
  | nil => simp [DefiniteList]
  | cons x xs ih => simp [DefiniteList, ih]

theorem DefinitePairs_iff (kvs : List (Item × Item)) :
    DefinitePairs kvs ↔ ∀ kv ∈ kvs, Definite kv.1 ∧ Definite kv.2 := by
  induction kvs with
  | nil => simp [DefinitePairs]
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [DefinitePairs, ih, and_assoc]

end Item

namespace RawItem

theorem deflateList_eq (xs : List RawItem) : deflateList xs = xs.map deflate := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [deflateList, ih]

theorem deflatePairs_eq (kvs : List (RawItem × RawItem)) :
    deflatePairs kvs = kvs.map fun kv => (deflate kv.1, deflate kv.2) := by
  induction kvs with
  | nil => rfl
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [deflatePairs, ih]

end RawItem

/-! ## Tree-level facts -/

namespace RawItem

theorem length_flatten_map_snd (cs : List (Width × List UInt8)) :
    ((cs.map Prod.snd).flatten).length = ((cs.map Prod.snd).flatten).length := rfl

/-- Wire-level and item-level deflation agree. -/
theorem toItem_deflate (r : RawItem) : r.deflate.toItem = r.toItem.deflate := by
  induction r using RawItem.rec' with
  | uint w n => rfl
  | nint w n => rfl
  | bytes w p => rfl
  | text w p => rfl
  | bytesIndef cs =>
    simp only [deflate, toItem, Item.deflate]
    split <;> rfl
  | textIndef cs =>
    simp only [deflate, toItem, Item.deflate]
    split <;> rfl
  | array w xs ih =>
    simp only [deflate, toItem, Item.deflate, deflateList_eq, toItemList_eq,
      Item.deflateList_eq, List.map_map]
    congr 1
    exact List.map_congr_left fun x hx => ih x hx
  | arrayIndef xs ih =>
    have hl : (deflateList xs).length = xs.length := by simp [deflateList_eq]
    have hmap : toItemList (deflateList xs) = Item.deflateList (toItemList xs) := by
      simp only [deflateList_eq, toItemList_eq, Item.deflateList_eq, List.map_map]
      exact List.map_congr_left fun x hx => ih x hx
    simp only [deflate, toItem, Item.deflate]
    have hl' : (toItemList xs).length = xs.length := by simp [toItemList_eq]
    by_cases h : xs.length < 2 ^ 64
    · simp [h, hl', toItem, hmap]
    · simp [h, hl', toItem, hmap]
  | map w kvs ih =>
    simp only [deflate, toItem, Item.deflate, deflatePairs_eq, toItemPairs_eq,
      Item.deflatePairs_eq, List.map_map]
    congr 1
    refine List.map_congr_left fun kv hkv => ?_
    simp [(ih kv hkv).1, (ih kv hkv).2]
  | mapIndef kvs ih =>
    have hmap : toItemPairs (deflatePairs kvs) = Item.deflatePairs (toItemPairs kvs) := by
      simp only [deflatePairs_eq, toItemPairs_eq, Item.deflatePairs_eq, List.map_map]
      refine List.map_congr_left fun kv hkv => ?_
      simp [(ih kv hkv).1, (ih kv hkv).2]
    simp only [deflate, toItem, Item.deflate]
    have hl' : (toItemPairs kvs).length = kvs.length := by simp [toItemPairs_eq]
    by_cases h : kvs.length < 2 ^ 64
    · simp [h, hl', toItem, hmap]
    · simp [h, hl', toItem, hmap]
  | tag w t x ih => simp [deflate, toItem, Item.deflate, ih]
  | simple v => rfl

/-- Deflation preserves well-formedness (new heads are preferred, and only
sizes below 2^64 get one). -/
theorem WF_deflate {r : RawItem} (hr : r.WF) : r.deflate.WF := by
  induction r using RawItem.rec' with
  | uint w n => exact hr
  | nint w n => exact hr
  | bytes w p => exact hr
  | text w p => exact hr
  | bytesIndef cs =>
    simp only [deflate]
    split
    · rename_i h; exact Width.preferred_fits h
    · exact hr
  | textIndef cs =>
    simp only [deflate]
    split
    · rename_i h; exact Width.preferred_fits h
    · exact hr
  | array w xs ih =>
    obtain ⟨hfit, hxs⟩ := hr
    rw [WFList_iff] at hxs
    refine ⟨by simpa [deflateList_eq] using hfit, ?_⟩
    rw [WFList_iff, deflateList_eq]
    simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    exact ih x hx (hxs x hx)
  | arrayIndef xs ih =>
    rw [WF, WFList_iff] at hr
    have hall : WFList (deflateList xs) := by
      rw [WFList_iff, deflateList_eq]
      simp only [List.mem_map]
      rintro _ ⟨x, hx, rfl⟩
      exact ih x hx (hr x hx)
    simp only [deflate]
    split
    · rename_i h
      exact ⟨by rw [show (deflateList xs).length = xs.length by simp [deflateList_eq]]
                exact Width.preferred_fits h, hall⟩
    · exact hall
  | map w kvs ih =>
    obtain ⟨hfit, hkvs⟩ := hr
    rw [WFPairs_iff] at hkvs
    refine ⟨by simpa [deflatePairs_eq] using hfit, ?_⟩
    rw [WFPairs_iff, deflatePairs_eq]
    simp only [List.mem_map]
    rintro _ ⟨kv, hkv, rfl⟩
    exact ⟨(ih kv hkv).1 (hkvs kv hkv).1, (ih kv hkv).2 (hkvs kv hkv).2⟩
  | mapIndef kvs ih =>
    rw [WF, WFPairs_iff] at hr
    have hall : WFPairs (deflatePairs kvs) := by
      rw [WFPairs_iff, deflatePairs_eq]
      simp only [List.mem_map]
      rintro _ ⟨kv, hkv, rfl⟩
      exact ⟨(ih kv hkv).1 (hr kv hkv).1, (ih kv hkv).2 (hr kv hkv).2⟩
    simp only [deflate]
    split
    · rename_i h
      exact ⟨by rw [show (deflatePairs kvs).length = kvs.length by simp [deflatePairs_eq]]
                exact Width.preferred_fits h, hall⟩
    · exact hall
  | tag w t x ih => exact ⟨hr.1, ih hr.2⟩
  | simple v => exact hr

/-- Deflation is idempotent on trees. -/
theorem deflate_deflate (r : RawItem) : r.deflate.deflate = r.deflate := by
  induction r using RawItem.rec' with
  | uint w n => rfl
  | nint w n => rfl
  | bytes w p => rfl
  | text w p => rfl
  | bytesIndef cs =>
    simp only [deflate]
    split
    · rfl
    · rename_i h; simp only [deflate, h, ↓reduceIte]
  | textIndef cs =>
    simp only [deflate]
    split
    · rfl
    · rename_i h; simp only [deflate, h, ↓reduceIte]
  | array w xs ih =>
    simp only [deflate, deflateList_eq, List.map_map]
    congr 1
    exact List.map_congr_left fun x hx => ih x hx
  | arrayIndef xs ih =>
    have hmap : deflateList (deflateList xs) = deflateList xs := by
      simp only [deflateList_eq, List.map_map]
      exact List.map_congr_left fun x hx => ih x hx
    have hl : (deflateList xs).length = xs.length := by simp [deflateList_eq]
    simp only [deflate]
    by_cases h : xs.length < 2 ^ 64
    · simp [h, deflate, hmap]
    · simp [h, deflate, hmap, hl]
  | map w kvs ih =>
    simp only [deflate, deflatePairs_eq, List.map_map]
    congr 1
    refine List.map_congr_left fun kv hkv => ?_
    simp [(ih kv hkv).1, (ih kv hkv).2]
  | mapIndef kvs ih =>
    have hmap : deflatePairs (deflatePairs kvs) = deflatePairs kvs := by
      simp only [deflatePairs_eq, List.map_map]
      refine List.map_congr_left fun kv hkv => ?_
      simp [(ih kv hkv).1, (ih kv hkv).2]
    have hl : (deflatePairs kvs).length = kvs.length := by simp [deflatePairs_eq]
    simp only [deflate]
    by_cases h : kvs.length < 2 ^ 64
    · simp [h, deflate, hmap]
    · simp [h, deflate, hmap, hl]
  | tag w t x ih => simp [deflate, ih]
  | simple v => rfl

/-- On a tree without indefinite-length items deflation changes nothing —
in particular non-preferred heads are kept. -/
theorem deflate_of_definite {r : RawItem} (h : r.Definite) : r.deflate = r := by
  induction r using RawItem.rec' with
  | uint w n => rfl
  | nint w n => rfl
  | bytes w p => rfl
  | text w p => rfl
  | bytesIndef cs => exact absurd h id
  | textIndef cs => exact absurd h id
  | array w xs ih =>
    simp only [Definite, DefiniteList_iff] at h
    simp only [deflate, deflateList_eq]
    congr 1
    exact (List.map_congr_left fun x hx => ih x hx (h x hx)).trans (List.map_id _)
  | arrayIndef xs ih => exact absurd h id
  | map w kvs ih =>
    simp only [Definite, DefinitePairs_iff] at h
    simp only [deflate, deflatePairs_eq]
    congr 1
    refine (List.map_congr_left fun kv hkv => ?_).trans (List.map_id _)
    rw [(ih kv hkv).1 (h kv hkv).1, (ih kv hkv).2 (h kv hkv).2]
    rfl
  | mapIndef kvs ih => exact absurd h id
  | tag w t x ih => simp only [Definite] at h; simp [deflate, ih h]
  | simple v => rfl

/-- **Definite-producing under the size hypothesis.** -/
theorem definite_deflate {r : RawItem} (h : r.toItem.IndefBounded) : r.deflate.Definite := by
  induction r using RawItem.rec' with
  | uint w n => trivial
  | nint w n => trivial
  | bytes w p => trivial
  | text w p => trivial
  | bytesIndef cs =>
    simp only [toItem, Item.IndefBounded] at h
    simp only [deflate, h, ↓reduceIte]
    trivial
  | textIndef cs =>
    simp only [toItem, Item.IndefBounded] at h
    simp only [deflate, h, ↓reduceIte]
    trivial
  | array w xs ih =>
    simp only [toItem, Item.IndefBounded, Item.IndefBoundedList_iff, toItemList_eq,
      List.mem_map] at h
    simp only [deflate, Definite, DefiniteList_iff, deflateList_eq, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    exact ih x hx (h _ ⟨x, hx, rfl⟩)
  | arrayIndef xs ih =>
    simp only [toItem, Item.IndefBounded, Item.IndefBoundedList_iff, toItemList_eq,
      List.mem_map, List.length_map] at h
    obtain ⟨hl, h⟩ := h
    simp only [deflate, hl, ↓reduceIte, Definite, DefiniteList_iff, deflateList_eq, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    exact ih x hx (h _ ⟨x, hx, rfl⟩)
  | map w kvs ih =>
    simp only [toItem, Item.IndefBounded, Item.IndefBoundedPairs_iff, toItemPairs_eq,
      List.mem_map] at h
    simp only [deflate, Definite, DefinitePairs_iff, deflatePairs_eq, List.mem_map]
    rintro _ ⟨kv, hkv, rfl⟩
    have := h _ ⟨kv, hkv, rfl⟩
    exact ⟨(ih kv hkv).1 this.1, (ih kv hkv).2 this.2⟩
  | mapIndef kvs ih =>
    simp only [toItem, Item.IndefBounded, Item.IndefBoundedPairs_iff, toItemPairs_eq,
      List.mem_map, List.length_map] at h
    obtain ⟨hl, h⟩ := h
    simp only [deflate, hl, ↓reduceIte, Definite, DefinitePairs_iff, deflatePairs_eq,
      List.mem_map]
    rintro _ ⟨kv, hkv, rfl⟩
    have := h _ ⟨kv, hkv, rfl⟩
    exact ⟨(ih kv hkv).1 this.1, (ih kv hkv).2 this.2⟩
  | tag w t x ih => exact ih h
  | simple v => trivial

/-- Wire-level and item-level definiteness agree. -/
theorem definite_iff_toItem (r : RawItem) : r.Definite ↔ r.toItem.Definite := by
  induction r using RawItem.rec' with
  | uint w n => exact Iff.rfl
  | nint w n => exact Iff.rfl
  | bytes w p => exact Iff.rfl
  | text w p => exact Iff.rfl
  | bytesIndef cs => exact Iff.rfl
  | textIndef cs => exact Iff.rfl
  | array w xs ih =>
    simp only [Definite, toItem, Item.Definite, DefiniteList_iff, Item.DefiniteList_iff,
      toItemList_eq, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact forall₂_congr fun x hx => ih x hx
  | arrayIndef xs ih => exact Iff.rfl
  | map w kvs ih =>
    simp only [Definite, toItem, Item.Definite, DefinitePairs_iff, Item.DefinitePairs_iff,
      toItemPairs_eq, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact forall₂_congr fun kv hkv => and_congr (ih kv hkv).1 (ih kv hkv).2
  | mapIndef kvs ih => exact Iff.rfl
  | tag w t x ih => exact ih
  | simple v => exact Iff.rfl

end RawItem

namespace Item

/-- Deflation never changes the data-model value (§2, §3.2.3). -/
theorem canonWith_deflate (ext : Bool) (x : Item) : x.deflate.canonWith ext = x.canonWith ext := by
  induction x using Item.rec' with
  | uint n => rfl
  | nint n => rfl
  | bytes p => rfl
  | text p => rfl
  | bytesIndef cs => simp only [deflate]; split <;> rfl
  | textIndef cs => simp only [deflate]; split <;> rfl
  | array xs ih =>
    simp only [deflate, canonWith, canonWithList_eq, deflateList_eq, List.map_map]
    congr 1
    exact List.map_congr_left fun x hx => ih x hx
  | arrayIndef xs ih =>
    have hmap : canonWithList ext (deflateList xs) = canonWithList ext xs := by
      simp only [canonWithList_eq, deflateList_eq, List.map_map]
      exact List.map_congr_left fun x hx => ih x hx
    simp only [deflate]
    split <;> simp [canonWith, hmap]
  | map kvs ih =>
    simp only [deflate, canonWith, canonWithPairs_eq, deflatePairs_eq, List.map_map]
    congr 2
    refine List.map_congr_left fun kv hkv => ?_
    simp [(ih kv hkv).1, (ih kv hkv).2]
  | mapIndef kvs ih =>
    have hmap : canonWithPairs ext (deflatePairs kvs) = canonWithPairs ext kvs := by
      simp only [canonWithPairs_eq, deflatePairs_eq, List.map_map]
      refine List.map_congr_left fun kv hkv => ?_
      simp [(ih kv hkv).1, (ih kv hkv).2]
    simp only [deflate]
    split <;> simp [canonWith, hmap]
  | tag t x ih => simp [deflate, canonWith, ih]
  | simple v => rfl

theorem equiv_deflate (x : Item) : Equiv x x.deflate := (canonWith_deflate false x).symm

theorem equivExt_deflate (x : Item) : EquivExt x x.deflate := (canonWith_deflate true x).symm

/-- Deflation commutes with the deterministic shape. -/
theorem normalise_deflate (x : Item) : x.deflate.normalise = x.normalise := by
  induction x using Item.rec' with
  | uint n => rfl
  | nint n => rfl
  | bytes p => rfl
  | text p => rfl
  | bytesIndef cs => simp only [deflate]; split <;> rfl
  | textIndef cs => simp only [deflate]; split <;> rfl
  | array xs ih =>
    simp only [deflate, normalise, normaliseList_eq, deflateList_eq, List.map_map]
    congr 1
    exact List.map_congr_left fun x hx => ih x hx
  | arrayIndef xs ih =>
    have hmap : normaliseList (deflateList xs) = normaliseList xs := by
      simp only [normaliseList_eq, deflateList_eq, List.map_map]
      exact List.map_congr_left fun x hx => ih x hx
    simp only [deflate]
    split <;> simp [normalise, hmap]
  | map kvs ih =>
    simp only [deflate, normalise, normalisePairs_eq, deflatePairs_eq, List.map_map]
    congr 2
    refine List.map_congr_left fun kv hkv => ?_
    simp [(ih kv hkv).1, (ih kv hkv).2]
  | mapIndef kvs ih =>
    have hmap : normalisePairs (deflatePairs kvs) = normalisePairs kvs := by
      simp only [normalisePairs_eq, deflatePairs_eq, List.map_map]
      refine List.map_congr_left fun kv hkv => ?_
      simp [(ih kv hkv).1, (ih kv hkv).2]
    simp only [deflate]
    split <;> simp [normalise, hmap]
  | tag t x ih => simp [deflate, normalise, ih]
  | simple v => rfl

/-- Deflation keeps the erasure of serialization choices. -/
theorem toDefinite_deflate (x : Item) : x.deflate.toDefinite = x.toDefinite := by
  induction x using Item.rec' with
  | uint n => rfl
  | nint n => rfl
  | bytes p => rfl
  | text p => rfl
  | bytesIndef cs => simp only [deflate]; split <;> rfl
  | textIndef cs => simp only [deflate]; split <;> rfl
  | array xs ih =>
    simp only [deflate, toDefinite, toDefiniteList_eq, deflateList_eq, List.map_map]
    congr 1
    exact List.map_congr_left fun x hx => ih x hx
  | arrayIndef xs ih =>
    have hmap : toDefiniteList (deflateList xs) = toDefiniteList xs := by
      simp only [toDefiniteList_eq, deflateList_eq, List.map_map]
      exact List.map_congr_left fun x hx => ih x hx
    simp only [deflate]
    split <;> simp [toDefinite, hmap]
  | map kvs ih =>
    simp only [deflate, toDefinite, toDefinitePairs_eq, deflatePairs_eq, List.map_map]
    congr 1
    refine List.map_congr_left fun kv hkv => ?_
    simp [(ih kv hkv).1, (ih kv hkv).2]
  | mapIndef kvs ih =>
    have hmap : toDefinitePairs (deflatePairs kvs) = toDefinitePairs kvs := by
      simp only [toDefinitePairs_eq, deflatePairs_eq, List.map_map]
      refine List.map_congr_left fun kv hkv => ?_
      simp [(ih kv hkv).1, (ih kv hkv).2]
    simp only [deflate]
    split <;> simp [toDefinite, hmap]
  | tag t x ih => simp [deflate, toDefinite, ih]
  | simple v => rfl

/-- Under the size hypothesis deflation is exactly the erasure. -/
theorem deflate_eq_toDefinite {x : Item} (h : x.IndefBounded) : x.deflate = x.toDefinite := by
  induction x using Item.rec' with
  | uint n => rfl
  | nint n => rfl
  | bytes p => rfl
  | text p => rfl
  | bytesIndef cs => simp only [IndefBounded] at h; simp only [deflate, toDefinite, h, ↓reduceIte]
  | textIndef cs => simp only [IndefBounded] at h; simp only [deflate, toDefinite, h, ↓reduceIte]
  | array xs ih =>
    simp only [IndefBounded, IndefBoundedList_iff] at h
    simp only [deflate, toDefinite, deflateList_eq, toDefiniteList_eq]
    congr 1
    exact List.map_congr_left fun x hx => ih x hx (h x hx)
  | arrayIndef xs ih =>
    simp only [IndefBounded, IndefBoundedList_iff] at h
    simp only [deflate, toDefinite, deflateList_eq, toDefiniteList_eq, h.1, ↓reduceIte]
    congr 1
    exact List.map_congr_left fun x hx => ih x hx (h.2 x hx)
  | map kvs ih =>
    simp only [IndefBounded, IndefBoundedPairs_iff] at h
    simp only [deflate, toDefinite, deflatePairs_eq, toDefinitePairs_eq]
    congr 1
    refine List.map_congr_left fun kv hkv => ?_
    simp [(ih kv hkv).1 (h kv hkv).1, (ih kv hkv).2 (h kv hkv).2]
  | mapIndef kvs ih =>
    simp only [IndefBounded, IndefBoundedPairs_iff] at h
    simp only [deflate, toDefinite, deflatePairs_eq, toDefinitePairs_eq, h.1, ↓reduceIte]
    congr 1
    refine List.map_congr_left fun kv hkv => ?_
    simp [(ih kv hkv).1 (h.2 kv hkv).1, (ih kv hkv).2 (h.2 kv hkv).2]
  | tag t x ih => simp only [IndefBounded] at h; simp [deflate, toDefinite, ih h]
  | simple v => rfl

end Item

/-! ## The wire-level theorems -/

theorem parseRaw_deflateIndefinite {bs : List UInt8} {r : RawItem} (h : parseRaw bs = some r) :
    parseRaw (deflateIndefinite bs) = some r.deflate := by
  have hwf := (parseRaw_eq_some_iff.1 h).1
  rw [deflateIndefinite, h]
  exact parseRaw_eq_some_iff.2 ⟨RawItem.WF_deflate hwf, rfl⟩

theorem deflateIndefinite_of_parseRaw_none {bs : List UInt8} (h : parseRaw bs = none) :
    deflateIndefinite bs = bs := by
  rw [deflateIndefinite, h]

theorem parseRaw_eq_none_of_parseWellFormed {bs : List UInt8} (h : parseWellFormed bs = none) :
    parseRaw bs = none := by
  unfold parseWellFormed at h
  split at h
  · simp at h
  · rename_i hr; exact hr

/-- **Syntax preservation, tree form.** Parsing the deflated wire gives the
deflated tree: same order, same tags, same keys and values; only indefinite
aggregates that fit a definite head become definite. Holds for every input. -/
theorem parseWellFormed_deflateIndefinite (bs : List UInt8) :
    parseWellFormed (deflateIndefinite bs) = (parseWellFormed bs).map Item.deflate := by
  cases h : parseRaw bs with
  | none =>
    rw [deflateIndefinite_of_parseRaw_none h]
    simp [parseWellFormed, h]
  | some r =>
    have h' := parseRaw_deflateIndefinite h
    simp [parseWellFormed, h, h', RawItem.toItem_deflate]

/-- **Syntax preservation, ∃ form.** Every well-formed input is deflated to a
well-formed input whose item is §5.6.1-equivalent (the same data-model
value). -/
theorem deflateIndefinite_exists_equiv {bs : List UInt8} {x : Item}
    (h : parseWellFormed bs = some x) :
    ∃ y, parseWellFormed (deflateIndefinite bs) = some y ∧ Item.Equiv x y ∧ Item.EquivExt x y :=
  ⟨x.deflate, by rw [parseWellFormed_deflateIndefinite, h]; rfl, Item.equiv_deflate x,
    Item.equivExt_deflate x⟩

/-- **Syntax preservation, erasure form.** Once the definite/indefinite
choice is erased, the parse of the deflated wire equals the parse of the
input. -/
theorem parseWellFormed_deflateIndefinite_toDefinite (bs : List UInt8) :
    (parseWellFormed (deflateIndefinite bs)).map Item.toDefinite =
      (parseWellFormed bs).map Item.toDefinite := by
  rw [parseWellFormed_deflateIndefinite]
  cases parseWellFormed bs <;> simp [Item.toDefinite_deflate]

/-- **Definite-producing, under the size hypothesis** (twice-amended
deliverable 2). The output is a well-formed wire with no indefinite-length
item, whose parse is exactly the input's parse with serialization choices
erased, hence §5.6.1-equivalent to it. -/
theorem deflateIndefinite_definite {bs : List UInt8} {x : Item}
    (h : parseWellFormed bs = some x) (hb : x.IndefBounded) :
    ∃ r, parseRaw (deflateIndefinite bs) = some r ∧ r.Definite ∧ r.toItem = x.toDefinite ∧
      Item.Equiv x r.toItem := by
  unfold parseWellFormed at h
  split at h
  · rename_i r hr
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨r.deflate, parseRaw_deflateIndefinite hr, RawItem.definite_deflate hb, ?_, ?_⟩
    · rw [RawItem.toItem_deflate, Item.deflate_eq_toDefinite hb]
    · rw [RawItem.toItem_deflate]; exact Item.equiv_deflate _
  · simp at h

/-- **Idempotence**, for every input. -/
theorem deflateIndefinite_idem (bs : List UInt8) :
    deflateIndefinite (deflateIndefinite bs) = deflateIndefinite bs := by
  cases h : parseRaw bs with
  | none => rw [deflateIndefinite_of_parseRaw_none h, deflateIndefinite_of_parseRaw_none h]
  | some r =>
    have h' := parseRaw_deflateIndefinite h
    have e1 : deflateIndefinite (deflateIndefinite bs) = r.deflate.deflate.encode := by
      rw [deflateIndefinite, h']
    have e2 : deflateIndefinite bs = r.deflate.encode := by rw [deflateIndefinite, h]
    rw [e1, e2, RawItem.deflate_deflate]

/-- **Commutation with `encodeDeterministic ∘ normalise`**, for every input:
deflating first does not change the core deterministic encoding. -/
theorem deflateIndefinite_normalise (bs : List UInt8) :
    (parseWellFormed (deflateIndefinite bs)).map (fun y => encodeDeterministic y.normalise) =
      (parseWellFormed bs).map (fun x => encodeDeterministic x.normalise) := by
  rw [parseWellFormed_deflateIndefinite]
  cases parseWellFormed bs <;> simp [Item.normalise_deflate]

/-- A wire with no indefinite-length item is left byte-for-byte unchanged,
including any non-preferred heads (I4: only indefinite items are rewritten). -/
theorem deflateIndefinite_of_definite {bs : List UInt8} {r : RawItem}
    (h : parseRaw bs = some r) (hd : r.Definite) : deflateIndefinite bs = bs := by
  have e : deflateIndefinite bs = r.deflate.encode := by rw [deflateIndefinite, h]
  rw [e, RawItem.deflate_of_definite hd]
  exact (parseRaw_eq_some_iff.1 h).2

/-! ## Every physically realisable wire satisfies the size hypothesis -/

theorem payload_le_encodeChunks (m : Nat) (cs : List (Width × List UInt8)) :
    ((cs.map Prod.snd).flatten).length ≤ (RawItem.encodeChunks m cs).length := by
  induction cs with
  | nil => simp [RawItem.encodeChunks]
  | cons c cs ih =>
    obtain ⟨w, p⟩ := c
    simp only [List.map_cons, List.flatten_cons, List.length_append, RawItem.encodeChunks]
    omega

theorem RawItem.indefBounded_of_encode_length_lt {r : RawItem} (hr : r.WF)
    (h : r.encode.length < 2 ^ 64) : r.toItem.IndefBounded := by
  induction r using RawItem.rec' with
  | uint w n => trivial
  | nint w n => trivial
  | bytes w p => trivial
  | text w p => trivial
  | bytesIndef cs =>
    have := payload_le_encodeChunks 2 cs
    simp only [RawItem.encode, List.length_cons, List.length_append, List.length_nil] at h
    show ((cs.map Prod.snd).flatten).length < 2 ^ 64
    omega
  | textIndef cs =>
    have := payload_le_encodeChunks 3 cs
    simp only [RawItem.encode, List.length_cons, List.length_append, List.length_nil] at h
    show ((cs.map Prod.snd).flatten).length < 2 ^ 64
    omega
  | array w xs ih =>
    obtain ⟨_, hxs⟩ := hr
    rw [RawItem.WFList_iff] at hxs
    simp only [RawItem.encode, List.length_append, RawItem.encodeList_eq] at h
    show Item.IndefBoundedList _
    rw [Item.IndefBoundedList_iff, RawItem.toItemList_eq]
    simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    have := length_le_flatten_of_mem (f := RawItem.encode) hx
    exact ih x hx (hxs x hx) (by omega)
  | arrayIndef xs ih =>
    rw [RawItem.WF, RawItem.WFList_iff] at hr
    simp only [RawItem.encode, List.length_cons, List.length_append, List.length_nil,
      RawItem.encodeList_eq] at h
    have hlen := length_le_flatten xs (f := RawItem.encode) fun x hx => RawItem.encode_ne_nil (hr x hx)
    refine ⟨by rw [RawItem.toItemList_eq, List.length_map]; omega, ?_⟩
    rw [Item.IndefBoundedList_iff, RawItem.toItemList_eq]
    simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    have := length_le_flatten_of_mem (f := RawItem.encode) hx
    exact ih x hx (hr x hx) (by omega)
  | map w kvs ih =>
    obtain ⟨_, hkvs⟩ := hr
    rw [RawItem.WFPairs_iff] at hkvs
    simp only [RawItem.encode, List.length_append, RawItem.encodePairs_eq] at h
    show Item.IndefBoundedPairs _
    rw [Item.IndefBoundedPairs_iff, RawItem.toItemPairs_eq]
    simp only [List.mem_map]
    rintro _ ⟨kv, hkv, rfl⟩
    have := length_le_flatten_of_mem (f := fun kv => kv.1.encode ++ kv.2.encode) hkv
    simp only [List.length_append] at this
    exact ⟨(ih kv hkv).1 (hkvs kv hkv).1 (by omega), (ih kv hkv).2 (hkvs kv hkv).2 (by omega)⟩
  | mapIndef kvs ih =>
    rw [RawItem.WF, RawItem.WFPairs_iff] at hr
    simp only [RawItem.encode, List.length_cons, List.length_append, List.length_nil,
      RawItem.encodePairs_eq] at h
    have hlen := length_le_flatten kvs (f := fun kv => kv.1.encode ++ kv.2.encode)
      fun kv hkv => by simp [RawItem.encode_ne_nil (hr kv hkv).1]
    refine ⟨by rw [RawItem.toItemPairs_eq, List.length_map]; omega, ?_⟩
    rw [Item.IndefBoundedPairs_iff, RawItem.toItemPairs_eq]
    simp only [List.mem_map]
    rintro _ ⟨kv, hkv, rfl⟩
    have := length_le_flatten_of_mem (f := fun kv => kv.1.encode ++ kv.2.encode) hkv
    simp only [List.length_append] at this
    exact ⟨(ih kv hkv).1 (hr kv hkv).1 (by omega), (ih kv hkv).2 (hr kv hkv).2 (by omega)⟩
  | tag w t x ih =>
    simp only [RawItem.encode, List.length_append] at h
    exact ih hr.2 (by omega)
  | simple v => trivial

/-- **The `bs.length < 2^64` corollary** (first amendment): each element,
chunk payload byte or pair occupies at least one wire byte, so every input
shorter than 2^64 bytes satisfies the size hypothesis — and is deflated to
a definite wire. -/
theorem indefBounded_of_length_lt {bs : List UInt8} {x : Item} (hlen : bs.length < 2 ^ 64)
    (h : parseWellFormed bs = some x) : x.IndefBounded := by
  obtain ⟨r, hwf, henc, rfl⟩ := parseWellFormed_eq_some_iff.1 h
  exact RawItem.indefBounded_of_encode_length_lt hwf (henc ▸ hlen)

theorem deflateIndefinite_definite_of_length_lt {bs : List UInt8} {x : Item}
    (hlen : bs.length < 2 ^ 64) (h : parseWellFormed bs = some x) :
    ∃ r, parseRaw (deflateIndefinite bs) = some r ∧ r.Definite ∧ r.toItem = x.toDefinite ∧
      Item.Equiv x r.toItem :=
  deflateIndefinite_definite h (indefBounded_of_length_lt hlen h)

end Cbor.Rfc8949
