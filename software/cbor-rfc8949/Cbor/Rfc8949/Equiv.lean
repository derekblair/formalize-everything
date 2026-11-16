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

theorem equivExt_textIndef (cs : List (List UInt8)) :
    EquivExt (.textIndef cs) (.text cs.flatten) := rfl

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

theorem not_equiv_tag_nint (t : Nat) (x : Item) (n : Nat) : ¬ Equiv (.tag t x) (.nint n) := by
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

/-! ### Maps as sets of pairs (§5.6.1) and deterministic canonicality -/

theorem encodePreferred_inj {x y : Item} (hx : x.WF) (hy : y.WF)
    (h : encodePreferred x = encodePreferred y) : x = y := by
  have hr : x.toRaw = y.toRaw := RawItem.encode_injective (Item.WF_toRaw hx) (Item.WF_toRaw hy) h
  have := congrArg RawItem.toItem hr
  simpa [Item.toRaw_toItem] using this

theorem entryLt_iff (p q : Item × Item) :
    entryLt p q = true ↔
      lexLt (encodePreferred p.1) (encodePreferred q.1) = true ∨
        (encodePreferred p.1 = encodePreferred q.1 ∧
          lexLt (encodePreferred p.2) (encodePreferred q.2) = true) := by
  simp [entryLt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]

theorem entryLt_irrefl (p : Item × Item) : entryLt p p = false := by
  simp [entryLt, lexLt_irrefl]

theorem entryLt_asymm {p q : Item × Item} (h : entryLt p q = true) : entryLt q p = false := by
  rw [entryLt_iff] at h
  cases hqp : entryLt q p
  · rfl
  · rw [entryLt_iff] at hqp
    rcases h with h | ⟨he, h⟩ <;> rcases hqp with h' | ⟨he', h'⟩
    · rw [lexLt_asymm h] at h'; exact h'.symm
    · rw [he'] at h; rw [lexLt_irrefl] at h; exact h.symm
    · rw [he] at h'; rw [lexLt_irrefl] at h'; exact h'.symm
    · rw [lexLt_asymm h] at h'; exact h'.symm

theorem entryLt_trans {p q r : Item × Item} (h1 : entryLt p q = true) (h2 : entryLt q r = true) :
    entryLt p r = true := by
  rw [entryLt_iff] at h1 h2 ⊢
  rcases h1 with h1 | ⟨he1, h1⟩ <;> rcases h2 with h2 | ⟨he2, h2⟩
  · exact Or.inl (lexLt_trans h1 h2)
  · rw [← he2]; exact Or.inl h1
  · rw [he1]; exact Or.inl h2
  · exact Or.inr ⟨he1.trans he2, lexLt_trans h1 h2⟩

theorem entryLt_total {p q : Item × Item} (hp : p.1.WF ∧ p.2.WF) (hq : q.1.WF ∧ q.2.WF)
    (hne : p ≠ q) : entryLt p q = true ∨ entryLt q p = true := by
  rw [entryLt_iff, entryLt_iff]
  by_cases h1 : encodePreferred p.1 = encodePreferred q.1
  · have hk : p.1 = q.1 := encodePreferred_inj hp.1 hq.1 h1
    have hv : p.2 ≠ q.2 := fun e => hne (Prod.ext hk e)
    have h2 : encodePreferred p.2 ≠ encodePreferred q.2 := fun e => hv (encodePreferred_inj hp.2 hq.2 e)
    rcases lexLt_total h2 with hlt | hlt
    · exact Or.inl (Or.inr ⟨h1, hlt⟩)
    · exact Or.inr (Or.inr ⟨h1.symm, hlt⟩)
  · rcases lexLt_total h1 with hlt | hlt
    · exact Or.inl (Or.inl hlt)
    · exact Or.inr (Or.inl hlt)

/-- Strictly increasing map entries under `entryLt`. -/
def EntryStrict : List (Item × Item) → Prop
  | [] => True
  | x :: xs => (∀ y ∈ xs, entryLt x y = true) ∧ EntryStrict xs

theorem mem_insertUniq (x z : Item × Item) :
    ∀ l : List (Item × Item), z ∈ insertUniq x l ↔ z = x ∨ z ∈ l
  | [] => by simp [insertUniq]
  | y :: ys => by
    simp only [insertUniq]
    split
    · rename_i hyx
      subst hyx
      simp only [List.mem_cons]
      exact ⟨fun h => Or.inr h, fun h => h.elim Or.inl id⟩
    · split
      · simp only [List.mem_cons, mem_insertUniq x z ys]
        constructor
        · rintro (rfl | rfl | hz)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hz)
        · rintro (rfl | rfl | hz)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hz)
      · simp [List.mem_cons]

theorem mem_sortUniq (z : Item × Item) :
    ∀ l : List (Item × Item), z ∈ sortUniq l ↔ z ∈ l
  | [] => by simp [sortUniq]
  | x :: xs => by simp [sortUniq, mem_insertUniq, mem_sortUniq z xs]

theorem entryStrict_insertUniq {x : Item × Item} (hx : x.1.WF ∧ x.2.WF) :
    ∀ {l : List (Item × Item)}, EntryStrict l → (∀ z ∈ l, z.1.WF ∧ z.2.WF) →
      EntryStrict (insertUniq x l)
  | [], _, _ => ⟨by simp, trivial⟩
  | y :: ys, ⟨hy, hys⟩, hwf => by
    simp only [insertUniq]
    split
    · exact ⟨hy, hys⟩
    · rename_i hyx
      split
      · rename_i hlt
        refine ⟨fun z hz => ?_,
          entryStrict_insertUniq hx hys (fun z hz => hwf z (by simp [hz]))⟩
        rw [mem_insertUniq] at hz
        rcases hz with rfl | hz
        · exact hlt
        · exact hy z hz
      · rename_i hlt
        have hywf := hwf y (by simp)
        have hxy : entryLt x y = true := by
          rcases entryLt_total hx hywf (Ne.symm hyx) with h | h
          · exact h
          · exact absurd h hlt
        refine ⟨fun z hz => ?_, ⟨hy, hys⟩⟩
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hxy
        · exact entryLt_trans hxy (hy z hz)

theorem entryStrict_sortUniq :
    ∀ {l : List (Item × Item)}, WFPairs l → EntryStrict (sortUniq l)
  | [], _ => trivial
  | kv :: kvs, hwf => by
    obtain ⟨k, v⟩ := kv
    simp only [WFPairs] at hwf
    refine entryStrict_insertUniq ⟨hwf.1, hwf.2.1⟩ (entryStrict_sortUniq hwf.2.2) ?_
    intro z hz
    rw [mem_sortUniq] at hz
    exact (WFPairs_iff kvs).1 hwf.2.2 z hz

theorem entryStrict_eq_of_mem_iff :
    ∀ {l₁ l₂ : List (Item × Item)}, EntryStrict l₁ → EntryStrict l₂ →
      (∀ z, z ∈ l₁ ↔ z ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: bs, _, _, h => absurd ((h b).2 (by simp)) (by simp)
  | a :: as, [], _, _, h => absurd ((h a).1 (by simp)) (by simp)
  | a :: as, b :: bs, ⟨ha, has⟩, ⟨hb, hbs⟩, h => by
    have hab : a = b := Classical.byContradiction fun hne => by
      have ha_in : a ∈ bs := by
        have := (h a).1 (by simp)
        simp only [List.mem_cons] at this
        exact this.resolve_left hne
      have hb_in : b ∈ as := by
        have := (h b).2 (by simp)
        simp only [List.mem_cons] at this
        exact this.resolve_left (Ne.symm hne)
      have h1 := ha b hb_in
      have h2 := hb a ha_in
      rw [entryLt_asymm h1] at h2
      exact Bool.noConfusion h2
    subst hab
    congr 1
    refine entryStrict_eq_of_mem_iff has hbs fun z => ?_
    constructor
    · intro hz
      have hne : z ≠ a := fun e => by
        subst e; have := ha z hz; rw [entryLt_irrefl] at this; exact Bool.noConfusion this
      have := (h z).1 (by simp [hz])
      simp only [List.mem_cons] at this
      exact this.resolve_left hne
    · intro hz
      have hne : z ≠ a := fun e => by
        subst e; have := hb z hz; rw [entryLt_irrefl] at this; exact Bool.noConfusion this
      have := (h z).2 (by simp [hz])
      simp only [List.mem_cons] at this
      exact this.resolve_left hne

/-- **Maps as sets of pairs (§5.6.1).** Two maps whose canonical entry pairs
are well-formed are equivalent iff they contain the same key/value pairs up to
`Item.Equiv`, regardless of order or duplicate identical entries. -/
theorem equiv_map_iff {kvs₁ kvs₂ : List (Item × Item)}
    (h₁ : WFPairs (canonWithPairs false kvs₁))
    (h₂ : WFPairs (canonWithPairs false kvs₂)) :
    Equiv (.map kvs₁) (.map kvs₂) ↔
      ∀ k v, (∃ kv ∈ kvs₁, Equiv kv.1 k ∧ Equiv kv.2 v) ↔
             (∃ kv ∈ kvs₂, Equiv kv.1 k ∧ Equiv kv.2 v) := by
  simp only [Equiv, canon, canonWith, map.injEq]
  constructor
  · intro heq k v
    have hmem : ∀ z, z ∈ canonWithPairs false kvs₁ ↔ z ∈ canonWithPairs false kvs₂ := fun z => by
      rw [← mem_sortUniq z (canonWithPairs false kvs₁), heq, mem_sortUniq]
    simp only [canonWithPairs_eq, List.mem_map, Prod.ext_iff] at hmem
    exact ⟨fun ⟨kv, hkv, hk, hv⟩ => by
        obtain ⟨kv', hkv', hk', hv'⟩ := (hmem (canonWith false kv.1, canonWith false kv.2)).1 ⟨kv, hkv, rfl, rfl⟩
        exact ⟨kv', hkv', hk'.trans hk, hv'.trans hv⟩,
      fun ⟨kv, hkv, hk, hv⟩ => by
        obtain ⟨kv', hkv', hk', hv'⟩ := (hmem (canonWith false kv.1, canonWith false kv.2)).2 ⟨kv, hkv, rfl, rfl⟩
        exact ⟨kv', hkv', hk'.trans hk, hv'.trans hv⟩⟩
  · intro hall
    refine entryStrict_eq_of_mem_iff (entryStrict_sortUniq h₁) (entryStrict_sortUniq h₂) fun z => ?_
    rw [mem_sortUniq, mem_sortUniq, canonWithPairs_eq, canonWithPairs_eq]
    simp only [List.mem_map]
    constructor
    · rintro ⟨kv, hkv, rfl⟩
      obtain ⟨kv', hkv', hk', hv'⟩ := (hall kv.1 kv.2).1 ⟨kv, hkv, rfl, rfl⟩
      exact ⟨kv', hkv', Prod.ext hk' hv'⟩
    · rintro ⟨kv, hkv, rfl⟩
      obtain ⟨kv', hkv', hk', hv'⟩ := (hall kv.1 kv.2).2 ⟨kv, hkv, rfl, rfl⟩
      exact ⟨kv', hkv', Prod.ext hk' hv'⟩

theorem equiv_mapIndef_iff {kvs₁ kvs₂ : List (Item × Item)}
    (h₁ : WFPairs (canonWithPairs false kvs₁))
    (h₂ : WFPairs (canonWithPairs false kvs₂)) :
    Equiv (.mapIndef kvs₁) (.mapIndef kvs₂) ↔
      ∀ k v, (∃ kv ∈ kvs₁, Equiv kv.1 k ∧ Equiv kv.2 v) ↔
             (∃ kv ∈ kvs₂, Equiv kv.1 k ∧ Equiv kv.2 v) :=
  equiv_map_iff h₁ h₂

theorem sortUniq_of_entryStrict : ∀ {l : List (Item × Item)}, EntryStrict l → sortUniq l = l
  | [], _ => rfl
  | x :: xs, ⟨hx, hxs⟩ => by
    simp only [sortUniq, sortUniq_of_entryStrict hxs]
    cases xs with
    | nil => rfl
    | cons y ys =>
      have hxy : entryLt x y = true := hx y (by simp)
      have hyx : entryLt y x = false := entryLt_asymm hxy
      have hne : y ≠ x := fun e => by subst e; rw [entryLt_irrefl] at hxy; exact Bool.noConfusion hxy
      simp [insertUniq, hne, hyx]

theorem entryStrict_of_keysStrict :
    ∀ {kvs : List (Item × Item)}, keysStrict kvs = true → EntryStrict kvs
  | [], _ => trivial
  | p :: rest, h =>
    ⟨fun z hz => by
        rw [entryLt_iff]
        exact Or.inl (keysStrict_head_lt p rest h z hz),
      entryStrict_of_keysStrict (keysStrict_tail p rest h)⟩

/-- Every item in core deterministic shape is already its own §5.6.1 basic
canonical representative. -/
theorem canon_of_isDeterministic {x : Item} (hx : x.isDeterministic = true) : x.canon = x := by
  unfold canon
  induction x using Item.rec' with
  | uint n => rfl
  | nint n => rfl
  | bytes p => rfl
  | text p => rfl
  | bytesIndef cs => simp [isDeterministic] at hx
  | textIndef cs => simp [isDeterministic] at hx
  | array xs ih =>
    simp only [isDeterministic, isDeterministicList_iff] at hx
    simp only [canonWith, canonWithList_eq]
    congr 1
    exact (List.map_congr_left fun x hx' => ih x hx' (hx x hx')).trans (List.map_id _)
  | arrayIndef xs ih => simp [isDeterministic] at hx
  | map kvs ih =>
    simp only [isDeterministic, Bool.and_eq_true, isDeterministicPairs_iff] at hx
    obtain ⟨hs, hd⟩ := hx
    simp only [canonWith]
    congr 1
    have hpairs : canonWithPairs false kvs = kvs := by
      rw [canonWithPairs_eq]
      refine (List.map_congr_left fun kv hkv => ?_).trans (List.map_id _)
      rw [(ih kv hkv).1 (hd kv hkv).1, (ih kv hkv).2 (hd kv hkv).2]
      rfl
    rw [hpairs]
    exact sortUniq_of_entryStrict (entryStrict_of_keysStrict hs)
  | mapIndef kvs ih => simp [isDeterministic] at hx
  | tag t x ih =>
    simp only [isDeterministic] at hx
    simp [canonWith, ih hx]
  | simple v => rfl

/-! ### Extended generic data model of tags 2 and 3 (§3.4.3, §5.6.1) -/

theorem encodeInt_injective {z₁ z₂ : Int} (h : encodeInt z₁ = encodeInt z₂) : z₁ = z₂ := by
  have hv := congrArg Item.intValue? h
  rw [intValue?_encodeInt, intValue?_encodeInt] at hv
  exact Option.some.inj hv

/-- Every well-formed integer or tag-2/3 bignum item has `encodeInt z` as its
extended canonical representative. -/
theorem canonExt_of_intValue? {x : Item} {z : Int} (hx : x.WF) (hv : x.intValue? = some z) :
    x.canonExt = encodeInt z := by
  unfold canonExt
  match x, hx, hv with
  | .uint n, hx, hv =>
    simp only [intValue?, Option.some.injEq] at hv
    simp only [WF] at hx
    subst hv
    rw [encodeInt, ite_eq_left (by omega), ite_eq_left (by omega)]
    simp [canonWith]
  | .nint n, hx, hv =>
    simp only [intValue?, Option.some.injEq] at hv
    simp only [WF] at hx
    subst hv
    have h1 : ¬ (0 : Int) ≤ -1 - (n : Int) := by omega
    have h2 : -2 ^ 64 ≤ -1 - (n : Int) := by omega
    rw [encodeInt, ite_eq_right h1, ite_eq_left h2]
    have h3 : (-1 - (-1 - (n : Int))).toNat = n := by omega
    simp [canonWith, h3]
  | .bytes _, _, hv | .text _, _, hv | .bytesIndef _, _, hv | .textIndef _, _, hv
  | .array _, _, hv | .arrayIndef _, _, hv | .map _, _, hv | .mapIndef _, _, hv
  | .simple _, _, hv =>
    simp [intValue?, bignumValue?] at hv
  | .tag t c, _, hv =>
    cases h2 : decide (t = 2) <;> cases h3 : decide (t = 3)
    · simp only [decide_eq_false_iff_not] at h2 h3
      simp [intValue?, bignumValue?, h2, h3] at hv
    · simp only [decide_eq_true_eq] at h3
      subst h3
      cases c <;> simp [intValue?, bignumValue?, byteContent?] at hv <;> subst hv <;> rfl
    · simp only [decide_eq_true_eq] at h2
      subst h2
      cases c <;> simp [intValue?, bignumValue?, byteContent?] at hv <;> subst hv <;> rfl
    · simp only [decide_eq_true_eq] at h2 h3; omega

/-- **Extended integer/bignum equivalence (§3.4.3, §5.6.1).** Two well-formed
integer/bignum items (major 0, major 1, definite or chunked tag 2/3, with or
without leading zero bytes) are equivalent in the extended generic data model
iff they denote the same mathematical integer `z : Int`. -/
theorem equivExt_of_intValue? {x y : Item} {z₁ z₂ : Int}
    (hx : x.WF) (hy : y.WF) (h₁ : x.intValue? = some z₁) (h₂ : y.intValue? = some z₂) :
    EquivExt x y ↔ z₁ = z₂ := by
  rw [EquivExt, canonExt_of_intValue? hx h₁, canonExt_of_intValue? hy h₂]
  exact ⟨encodeInt_injective, fun h => h ▸ rfl⟩

/-- Major-type-0 integer `n < 2^64` equals any tag-2 bignum with `beValue p = n`. -/
theorem equivExt_uint_tag2 {n : Nat} {p : List UInt8} (hn : n < 2 ^ 64) (hp : beValue p = n) :
    EquivExt (.uint n) (.tag 2 (.bytes p)) := by
  simp only [EquivExt, canonExt, canonWith, bignumOf, ↓reduceIte, hp]
  rw [encodeInt, ite_eq_left (by omega), ite_eq_left (by omega)]
  simp

/-- Major-type-1 integer `-1 - n` (`n < 2^64`) equals any tag-3 bignum with `beValue p = n`. -/
theorem equivExt_nint_tag3 {n : Nat} {p : List UInt8} (hn : n < 2 ^ 64) (hp : beValue p = n) :
    EquivExt (.nint n) (.tag 3 (.bytes p)) := by
  have hne : (3 : Nat) ≠ 2 := by decide
  simp only [EquivExt, canonExt, canonWith, bignumOf, hne, ↓reduceIte, hp]
  have h1 : ¬ (0 : Int) ≤ -1 - (n : Int) := by omega
  have h2 : -2 ^ 64 ≤ -1 - (n : Int) := by omega
  rw [encodeInt, ite_eq_right h1, ite_eq_left h2]
  have h3 : (-1 - (-1 - (n : Int))).toNat = n := by omega
  simp [h3]

/-- `0` and `2(h'')` are equivalent in the extended model (§3.4.3) and distinct
in the basic model (§5.6.1). -/
theorem equivExt_zero_tag2_empty : EquivExt (.uint 0) (.tag 2 (.bytes [])) :=
  equivExt_uint_tag2 (by decide) rfl

theorem not_equiv_zero_tag2_empty : ¬ Equiv (.uint 0) (.tag 2 (.bytes [])) :=
  fun h => not_equiv_tag_uint 2 (.bytes []) 0 h.symm

/-- Indefinite-length bignum byte strings equal definite ones under `EquivExt`. -/
theorem equivExt_tag2_indef (cs : List (List UInt8)) :
    EquivExt (.tag 2 (.bytesIndef cs)) (.tag 2 (.bytes cs.flatten)) := rfl

theorem equivExt_tag3_indef (cs : List (List UInt8)) :
    EquivExt (.tag 3 (.bytesIndef cs)) (.tag 3 (.bytes cs.flatten)) := rfl

/-- Leading zero bytes in tag 2/3 bignums are invisible under `EquivExt`. -/
theorem equivExt_tag2_leading_zeros (k : Nat) (p : List UInt8) :
    EquivExt (.tag 2 (.bytes (List.replicate k 0 ++ p))) (.tag 2 (.bytes p)) := by
  simp [EquivExt, canonExt, canonWith, bignumOf, beValue_zeros_append]

theorem equivExt_tag3_leading_zeros (k : Nat) (p : List UInt8) :
    EquivExt (.tag 3 (.bytes (List.replicate k 0 ++ p))) (.tag 3 (.bytes p)) := by
  simp [EquivExt, canonExt, canonWith, bignumOf, beValue_zeros_append]

end Item

end Cbor.Rfc8949
