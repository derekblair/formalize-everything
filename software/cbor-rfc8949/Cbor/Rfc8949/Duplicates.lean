/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Equiv

/-!
# Duplicate keys: strict rejection and first-wins collapse (§5.3.1, §5.6, §5.6.1)

§5.3.1: "a generic decoder that gets a CBOR map item that has duplicate keys
will decode to a map with only one instance of that key, or it might stop
processing altogether". §5.6 lists the decoder choices, including rejecting
such maps and delivering "only the final (or first) entry out of the entries
with the same key". This module formalizes, for both the basic generic data
model (`Item.Equiv`) and the extended one of tags 2/3 (`Item.EquivExt`):

* `decodeStrict` — reject any map, at any depth, with two equivalent keys;
* `decodeFirstWins` — collapse each map, bottom-up, to the first entry of
  each equivalence class of keys.

`firstWins` is characterized exactly (`firstWins_sublist`,
`firstWins_nodup`, `firstWins_cover`, `firstWins_first`), the collapsed
result is duplicate-free at every depth (`noDupKeys_collapse`), and the two
decoders agree exactly on the inputs the strict one accepts. Because
equivalence is §5.6.1's, keys that differ only by indefinite-length
chunking or containers are duplicates, and in the extended model so are
bignums and integers of equal value.
-/

namespace Cbor.Rfc8949

/-- Which generic data model decides key equivalence. -/
inductive DataModel where
  /-- The basic generic data model (§2, §5.6.1): bignums are tags. -/
  | basic
  /-- The extended generic data model of tags 2 and 3 (§2.1, §3.4.3). -/
  | extended
  deriving DecidableEq, Repr

/-- The canonical-representative function of a data model. -/
def DataModel.key : DataModel → Item → Item
  | .basic => Item.canon
  | .extended => Item.canonExt

/-- One-level first-wins pass: `seen` holds the canonical keys already kept. -/
def firstWinsAux (key : Item → Item) : List Item → List (Item × Item) → List (Item × Item)
  | _, [] => []
  | seen, kv :: kvs =>
    if key kv.1 ∈ seen then firstWinsAux key seen kvs
    else kv :: firstWinsAux key (key kv.1 :: seen) kvs

/-- Keep the first entry of each key-equivalence class, in order. -/
def firstWins (key : Item → Item) (kvs : List (Item × Item)) : List (Item × Item) :=
  firstWinsAux key [] kvs

/-- No two entries have equivalent keys. -/
def keysNodup (key : Item → Item) (kvs : List (Item × Item)) : Bool :=
  decide (kvs.map fun kv => key kv.1).Nodup

namespace Item

mutual
/-- No map anywhere in the item has two equivalent keys. -/
def noDupKeys (key : Item → Item) : Item → Bool
  | .array xs => noDupKeysList key xs
  | .arrayIndef xs => noDupKeysList key xs
  | .map kvs => keysNodup key kvs && noDupKeysPairs key kvs
  | .mapIndef kvs => keysNodup key kvs && noDupKeysPairs key kvs
  | .tag _ x => noDupKeys key x
  | _ => true
def noDupKeysList (key : Item → Item) : List Item → Bool
  | [] => true
  | x :: xs => noDupKeys key x && noDupKeysList key xs
def noDupKeysPairs (key : Item → Item) : List (Item × Item) → Bool
  | [] => true
  | (k, v) :: kvs => noDupKeys key k && noDupKeys key v && noDupKeysPairs key kvs
end

mutual
/-- Bottom-up first-wins collapse of every map; definite/indefinite choices
and all other structure are kept. -/
def collapse (key : Item → Item) : Item → Item
  | .array xs => .array (collapseList key xs)
  | .arrayIndef xs => .arrayIndef (collapseList key xs)
  | .map kvs => .map (firstWins key (collapsePairs key kvs))
  | .mapIndef kvs => .mapIndef (firstWins key (collapsePairs key kvs))
  | .tag t x => .tag t (collapse key x)
  | x => x
def collapseList (key : Item → Item) : List Item → List Item
  | [] => []
  | x :: xs => collapse key x :: collapseList key xs
def collapsePairs (key : Item → Item) : List (Item × Item) → List (Item × Item)
  | [] => []
  | (k, v) :: kvs => (collapse key k, collapse key v) :: collapsePairs key kvs
end

end Item

/-- The strict generic decoder: well-formed input whose maps have no
duplicate keys under the data model's equivalence. -/
def decodeStrict (dm : DataModel) (bs : List UInt8) : Option Item :=
  match parseWellFormed bs with
  | some x => if x.noDupKeys dm.key then some x else none
  | none => none

/-- The first-wins generic decoder: well-formed input with every map
collapsed to one instance of each key (§5.3.1, §5.6). -/
def decodeFirstWins (dm : DataModel) (bs : List UInt8) : Option Item :=
  match parseWellFormed bs with
  | some x => some (x.collapse dm.key)
  | none => none

/-! ## First-wins at one level -/

section FirstWins

variable (key : Item → Item)

theorem firstWinsAux_sublist : ∀ (seen : List Item) (l : List (Item × Item)),
    (firstWinsAux key seen l).Sublist l
  | _, [] => List.Sublist.slnil
  | seen, kv :: kvs => by
    simp only [firstWinsAux]
    split
    · exact (firstWinsAux_sublist seen kvs).cons kv
    · exact (firstWinsAux_sublist _ kvs).cons_cons kv

theorem firstWinsAux_not_seen : ∀ (seen : List Item) (l : List (Item × Item)),
    ∀ lw ∈ firstWinsAux key seen l, key lw.1 ∉ seen
  | _, [] => by simp [firstWinsAux]
  | seen, kv :: kvs => by
    simp only [firstWinsAux]
    split
    · exact firstWinsAux_not_seen seen kvs
    · rename_i h
      intro lw hlw
      simp only [List.mem_cons] at hlw
      rcases hlw with rfl | hlw
      · exact h
      · have := firstWinsAux_not_seen _ kvs lw hlw
        simp only [List.mem_cons, not_or] at this
        exact this.2

theorem firstWinsAux_nodup : ∀ (seen : List Item) (l : List (Item × Item)),
    ((firstWinsAux key seen l).map fun kv => key kv.1).Nodup
  | _, [] => by simp [firstWinsAux]
  | seen, kv :: kvs => by
    simp only [firstWinsAux]
    split
    · exact firstWinsAux_nodup seen kvs
    · simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
      refine ⟨fun lw hlw heq => ?_, firstWinsAux_nodup _ kvs⟩
      have := firstWinsAux_not_seen key _ kvs lw hlw
      simp [heq] at this

theorem firstWinsAux_cover : ∀ (seen : List Item) (l : List (Item × Item)),
    ∀ kv ∈ l, key kv.1 ∈ seen ∨ ∃ lw ∈ firstWinsAux key seen l, key lw.1 = key kv.1
  | _, [] => by simp
  | seen, kv :: kvs => by
    intro x hx
    simp only [List.mem_cons] at hx
    simp only [firstWinsAux]
    split
    · rename_i h
      rcases hx with rfl | hx
      · exact Or.inl h
      · exact firstWinsAux_cover seen kvs x hx
    · rcases hx with rfl | hx
      · exact Or.inr ⟨x, by simp, rfl⟩
      · rcases firstWinsAux_cover (key kv.1 :: seen) kvs x hx with h | ⟨lw, hlw, heq⟩
        · simp only [List.mem_cons] at h
          rcases h with h | h
          · exact Or.inr ⟨kv, by simp, h.symm⟩
          · exact Or.inl h
        · exact Or.inr ⟨lw, by simp [hlw], heq⟩

theorem firstWinsAux_first : ∀ (seen : List Item) (l : List (Item × Item)),
    ∀ lw ∈ firstWinsAux key seen l,
      ∃ pre post, l = pre ++ lw :: post ∧ ∀ kv ∈ pre, key kv.1 ∈ seen ∨ key kv.1 ≠ key lw.1
  | _, [] => by simp [firstWinsAux]
  | seen, kv :: kvs => by
    intro lw hlw
    simp only [firstWinsAux] at hlw
    split at hlw
    · rename_i h
      obtain ⟨pre, post, hl, hpre⟩ := firstWinsAux_first seen kvs lw hlw
      refine ⟨kv :: pre, post, by simp [hl], ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inl h
      · exact hpre x hx
    · rename_i h
      simp only [List.mem_cons] at hlw
      rcases hlw with rfl | hlw
      · exact ⟨[], kvs, rfl, by simp⟩
      · obtain ⟨pre, post, hl, hpre⟩ := firstWinsAux_first _ kvs lw hlw
        refine ⟨kv :: pre, post, by simp [hl], ?_⟩
        have hne : key lw.1 ≠ key kv.1 := by
          have := firstWinsAux_not_seen key _ kvs lw hlw
          simp only [List.mem_cons, not_or] at this
          exact this.1
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inr (Ne.symm hne)
        · rcases hpre x hx with h' | h'
          · simp only [List.mem_cons] at h'
            rcases h' with h' | h'
            · exact Or.inr (by rw [h']; exact Ne.symm hne)
            · exact Or.inl h'
          · exact Or.inr h'

theorem firstWinsAux_of_nodup : ∀ (seen : List Item) (l : List (Item × Item)),
    (l.map fun kv => key kv.1).Nodup → (∀ kv ∈ l, key kv.1 ∉ seen) →
      firstWinsAux key seen l = l
  | _, [], _, _ => rfl
  | seen, kv :: kvs, hnd, hseen => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    simp only [firstWinsAux, hseen kv (by simp), ↓reduceIte]
    congr 1
    apply firstWinsAux_of_nodup _ kvs hnd.2
    intro x hx
    simp only [List.mem_cons, not_or]
    exact ⟨fun h => hnd.1 x hx h, hseen x (by simp [hx])⟩

/-- First-wins keeps entries in their original order. -/
theorem firstWins_sublist (l : List (Item × Item)) : (firstWins key l).Sublist l :=
  firstWinsAux_sublist key [] l

/-- First-wins leaves no two equivalent keys. -/
theorem firstWins_nodup (l : List (Item × Item)) :
    ((firstWins key l).map fun kv => key kv.1).Nodup :=
  firstWinsAux_nodup key [] l

/-- Every input key keeps exactly one representative (with `firstWins_nodup`). -/
theorem firstWins_cover (l : List (Item × Item)) :
    ∀ kv ∈ l, ∃ lw ∈ firstWins key l, key lw.1 = key kv.1 := by
  intro kv hkv
  rcases firstWinsAux_cover key [] l kv hkv with h | h
  · simp at h
  · exact h

/-- Each kept entry is the first entry of the input with that key class
(first wins, value included). -/
theorem firstWins_first (l : List (Item × Item)) :
    ∀ lw ∈ firstWins key l,
      ∃ pre post, l = pre ++ lw :: post ∧ ∀ kv ∈ pre, key kv.1 ≠ key lw.1 := by
  intro lw hlw
  obtain ⟨pre, post, hl, hpre⟩ := firstWinsAux_first key [] l lw hlw
  exact ⟨pre, post, hl, fun kv hkv => (hpre kv hkv).resolve_left (by simp)⟩

/-- On a map without duplicate keys first-wins changes nothing. -/
theorem firstWins_of_nodup {l : List (Item × Item)} (h : (l.map fun kv => key kv.1).Nodup) :
    firstWins key l = l :=
  firstWinsAux_of_nodup key [] l h (by simp)

end FirstWins

/-! ## Collapse at every depth -/

namespace Item

theorem collapseList_eq (key : Item → Item) (xs : List Item) :
    collapseList key xs = xs.map (collapse key) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [collapseList, ih]

theorem collapsePairs_eq (key : Item → Item) (kvs : List (Item × Item)) :
    collapsePairs key kvs = kvs.map fun kv => (collapse key kv.1, collapse key kv.2) := by
  induction kvs with
  | nil => rfl
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [collapsePairs, ih]

theorem noDupKeysList_iff (key : Item → Item) (xs : List Item) :
    noDupKeysList key xs = true ↔ ∀ x ∈ xs, noDupKeys key x = true := by
  induction xs with
  | nil => simp [noDupKeysList]
  | cons x xs ih => simp [noDupKeysList, ih]

theorem noDupKeysPairs_iff (key : Item → Item) (kvs : List (Item × Item)) :
    noDupKeysPairs key kvs = true ↔
      ∀ kv ∈ kvs, noDupKeys key kv.1 = true ∧ noDupKeys key kv.2 = true := by
  induction kvs with
  | nil => simp [noDupKeysPairs]
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [noDupKeysPairs, ih, and_assoc]

/-- The first-wins collapse is duplicate-free at every depth. -/
theorem noDupKeys_collapse (key : Item → Item) (x : Item) :
    (x.collapse key).noDupKeys key = true := by
  induction x using Item.rec' with
  | uint n => rfl
  | nint n => rfl
  | bytes p => rfl
  | text p => rfl
  | bytesIndef cs => rfl
  | textIndef cs => rfl
  | array xs ih =>
    simp only [collapse, noDupKeys, noDupKeysList_iff, collapseList_eq, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩; exact ih x hx
  | arrayIndef xs ih =>
    simp only [collapse, noDupKeys, noDupKeysList_iff, collapseList_eq, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩; exact ih x hx
  | map kvs ih =>
    simp only [collapse, noDupKeys, Bool.and_eq_true, keysNodup, decide_eq_true_eq]
    refine ⟨firstWins_nodup key _, (noDupKeysPairs_iff key _).2 fun kv hkv => ?_⟩
    have hmem := (firstWins_sublist key _).subset hkv
    rw [collapsePairs_eq, List.mem_map] at hmem
    obtain ⟨kv', hkv', rfl⟩ := hmem
    exact ⟨(ih kv' hkv').1, (ih kv' hkv').2⟩
  | mapIndef kvs ih =>
    simp only [collapse, noDupKeys, Bool.and_eq_true, keysNodup, decide_eq_true_eq]
    refine ⟨firstWins_nodup key _, (noDupKeysPairs_iff key _).2 fun kv hkv => ?_⟩
    have hmem := (firstWins_sublist key _).subset hkv
    rw [collapsePairs_eq, List.mem_map] at hmem
    obtain ⟨kv', hkv', rfl⟩ := hmem
    exact ⟨(ih kv' hkv').1, (ih kv' hkv').2⟩
  | tag t x ih => exact ih
  | simple v => rfl

/-- An item without duplicate keys is left unchanged by the collapse. -/
theorem collapse_of_noDupKeys (key : Item → Item) {x : Item} (h : x.noDupKeys key = true) :
    x.collapse key = x := by
  induction x using Item.rec' with
  | uint n => rfl
  | nint n => rfl
  | bytes p => rfl
  | text p => rfl
  | bytesIndef cs => rfl
  | textIndef cs => rfl
  | array xs ih =>
    simp only [noDupKeys, noDupKeysList_iff] at h
    simp only [collapse, collapseList_eq]
    congr 1
    exact (List.map_congr_left fun x hx => ih x hx (h x hx)).trans (List.map_id _)
  | arrayIndef xs ih =>
    simp only [noDupKeys, noDupKeysList_iff] at h
    simp only [collapse, collapseList_eq]
    congr 1
    exact (List.map_congr_left fun x hx => ih x hx (h x hx)).trans (List.map_id _)
  | map kvs ih =>
    simp only [noDupKeys, Bool.and_eq_true, keysNodup, decide_eq_true_eq,
      noDupKeysPairs_iff] at h
    obtain ⟨hnd, hkvs⟩ := h
    have hc : collapsePairs key kvs = kvs := by
      rw [collapsePairs_eq]
      refine (List.map_congr_left fun kv hkv => ?_).trans (List.map_id _)
      rw [(ih kv hkv).1 (hkvs kv hkv).1, (ih kv hkv).2 (hkvs kv hkv).2]
      rfl
    simp only [collapse, hc, firstWins_of_nodup key hnd]
  | mapIndef kvs ih =>
    simp only [noDupKeys, Bool.and_eq_true, keysNodup, decide_eq_true_eq,
      noDupKeysPairs_iff] at h
    obtain ⟨hnd, hkvs⟩ := h
    have hc : collapsePairs key kvs = kvs := by
      rw [collapsePairs_eq]
      refine (List.map_congr_left fun kv hkv => ?_).trans (List.map_id _)
      rw [(ih kv hkv).1 (hkvs kv hkv).1, (ih kv hkv).2 (hkvs kv hkv).2]
      rfl
    simp only [collapse, hc, firstWins_of_nodup key hnd]
  | tag t x ih => simp only [noDupKeys] at h; simp [collapse, ih h]
  | simple v => rfl

end Item

/-! ## The two decoders, side by side -/

theorem decodeStrict_eq_some_iff {dm : DataModel} {bs : List UInt8} {x : Item} :
    decodeStrict dm bs = some x ↔ parseWellFormed bs = some x ∧ x.noDupKeys dm.key = true := by
  unfold decodeStrict
  cases hp : parseWellFormed bs with
  | none => simp
  | some y =>
    simp only [Option.some.injEq]
    by_cases hd : y.noDupKeys dm.key = true
    · simp only [hd, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, hd⟩
      · rintro ⟨rfl, _⟩; rfl
    · simp only [hd, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      rintro rfl; exact hd

theorem decodeFirstWins_eq_some_iff {dm : DataModel} {bs : List UInt8} {y : Item} :
    decodeFirstWins dm bs = some y ↔ ∃ x, parseWellFormed bs = some x ∧ y = x.collapse dm.key := by
  unfold decodeFirstWins
  cases hp : parseWellFormed bs with
  | none => simp
  | some x =>
    simp only [Option.some.injEq]
    constructor
    · intro h; exact ⟨x, rfl, h.symm⟩
    · rintro ⟨x', rfl, rfl⟩; rfl

/-- First-wins output never has duplicate keys. -/
theorem decodeFirstWins_noDupKeys {dm : DataModel} {bs : List UInt8} {y : Item}
    (h : decodeFirstWins dm bs = some y) : y.noDupKeys dm.key = true := by
  obtain ⟨x, _, rfl⟩ := decodeFirstWins_eq_some_iff.1 h
  exact Item.noDupKeys_collapse _ x

/-- Where the strict decoder accepts, first-wins returns the same item. -/
theorem decodeFirstWins_of_decodeStrict {dm : DataModel} {bs : List UInt8} {x : Item}
    (h : decodeStrict dm bs = some x) : decodeFirstWins dm bs = some x := by
  obtain ⟨hp, hnd⟩ := decodeStrict_eq_some_iff.1 h
  exact decodeFirstWins_eq_some_iff.2 ⟨x, hp, (Item.collapse_of_noDupKeys _ hnd).symm⟩

/-- On well-formed input, the strict decoder rejects exactly when some map
has two equivalent keys; first-wins then returns a different, duplicate-free
item. -/
theorem decodeStrict_none_iff {dm : DataModel} {bs : List UInt8} {x : Item}
    (hp : parseWellFormed bs = some x) :
    decodeStrict dm bs = none ↔ x.noDupKeys dm.key = false := by
  unfold decodeStrict
  rw [hp]
  cases h : x.noDupKeys dm.key <;> simp [h]

theorem decodeFirstWins_ne_of_dup {dm : DataModel} {bs : List UInt8} {x : Item}
    (hdup : x.noDupKeys dm.key = false) : decodeFirstWins dm bs ≠ some x := by
  intro h
  have := decodeFirstWins_noDupKeys h
  rw [hdup] at this
  exact Bool.false_ne_true this

end Cbor.Rfc8949
