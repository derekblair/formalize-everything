/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Grammar
import Cbor.Rfc8949.Lex

/-!
# Core deterministic encoding (§4.2.1) and the strict decoder

`Item.normalise` rewrites an item into deterministic shape: indefinite
strings become the definite string of their concatenated chunks (§3.2.3),
indefinite arrays and maps become definite, and every map's entries are
stably sorted by the bytewise lexicographic order of their keys'
deterministic encodings (§4.2.1). `encodeDeterministic x` is the preferred
serialization of `normalise x`.

`decodeDeterministic` is the strict decoder (I4 naming): it accepts exactly
the inputs that are the core deterministic encoding of a valid item —
preferred heads, no indefinite lengths, keys in strictly increasing
bytewise order (so no two keys share a deterministic encoding), and text
strings that are valid UTF-8 (§5.3.1). `Cbor.Rfc8949.Equiv` proves that the
strict key order also rules out duplicate keys under §5.6.1 equivalence.
-/

namespace Cbor.Rfc8949

/-! ## UTF-8 validity (RFC 3629 §4 / Unicode Table 3-7), used for §5.3.1 -/

/-- A continuation byte `80..BF`. -/
def isCont (b : UInt8) : Bool := 0x80 ≤ b.toNat && b.toNat ≤ 0xBF

/-- Byte in the closed range `lo..hi`. -/
def inRange (b : UInt8) (lo hi : Nat) : Bool := lo ≤ b.toNat && b.toNat ≤ hi

/-- Well-formed UTF-8, row by row from Unicode Table 3-7. -/
def utf8Valid : List UInt8 → Bool
  | [] => true
  | b :: bs =>
    if b.toNat < 0x80 then utf8Valid bs
    else if 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF then
      match bs with
      | c :: bs' => isCont c && utf8Valid bs'
      | [] => false
    else if b.toNat = 0xE0 then
      match bs with
      | c₁ :: c₂ :: bs' => inRange c₁ 0xA0 0xBF && isCont c₂ && utf8Valid bs'
      | _ => false
    else if (0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC) ∨ b.toNat = 0xEE ∨ b.toNat = 0xEF then
      match bs with
      | c₁ :: c₂ :: bs' => isCont c₁ && isCont c₂ && utf8Valid bs'
      | _ => false
    else if b.toNat = 0xED then
      match bs with
      | c₁ :: c₂ :: bs' => inRange c₁ 0x80 0x9F && isCont c₂ && utf8Valid bs'
      | _ => false
    else if b.toNat = 0xF0 then
      match bs with
      | c₁ :: c₂ :: c₃ :: bs' => inRange c₁ 0x90 0xBF && isCont c₂ && isCont c₃ && utf8Valid bs'
      | _ => false
    else if 0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3 then
      match bs with
      | c₁ :: c₂ :: c₃ :: bs' => isCont c₁ && isCont c₂ && isCont c₃ && utf8Valid bs'
      | _ => false
    else if b.toNat = 0xF4 then
      match bs with
      | c₁ :: c₂ :: c₃ :: bs' => inRange c₁ 0x80 0x8F && isCont c₂ && isCont c₃ && utf8Valid bs'
      | _ => false
    else false

namespace Item

mutual
/-- Every text string — definite, or each chunk of an indefinite one
(§3.2.3) — is valid UTF-8 (§5.3.1). -/
def textValid : Item → Bool
  | .text p => utf8Valid p
  | .textIndef cs => cs.all utf8Valid
  | .array xs => textValidList xs
  | .arrayIndef xs => textValidList xs
  | .map kvs => textValidPairs kvs
  | .mapIndef kvs => textValidPairs kvs
  | .tag _ x => textValid x
  | _ => true
def textValidList : List Item → Bool
  | [] => true
  | x :: xs => textValid x && textValidList xs
def textValidPairs : List (Item × Item) → Bool
  | [] => true
  | (k, v) :: kvs => textValid k && textValid v && textValidPairs kvs
end

end Item

/-- Map entries ordered by the bytewise order of their keys' encodings. -/
def keyLt (p q : Item × Item) : Bool := lexLt (encodePreferred p.1) (encodePreferred q.1)

namespace Item

mutual
/-- Deterministic shape (§4.2.1): definite lengths throughout and stably
key-sorted maps. -/
def normalise : Item → Item
  | .uint n => .uint n
  | .nint n => .nint n
  | .bytes p => .bytes p
  | .text p => .text p
  | .bytesIndef cs => .bytes cs.flatten
  | .textIndef cs => .text cs.flatten
  | .array xs => .array (normaliseList xs)
  | .arrayIndef xs => .array (normaliseList xs)
  | .map kvs => .map (sortBy keyLt (normalisePairs kvs))
  | .mapIndef kvs => .map (sortBy keyLt (normalisePairs kvs))
  | .tag t x => .tag t (normalise x)
  | .simple v => .simple v
def normaliseList : List Item → List Item
  | [] => []
  | x :: xs => normalise x :: normaliseList xs
def normalisePairs : List (Item × Item) → List (Item × Item)
  | [] => []
  | (k, v) :: kvs => (normalise k, normalise v) :: normalisePairs kvs
end

/-- Consecutive keys strictly increase in bytewise order of their encodings. -/
def keysStrict : List (Item × Item) → Bool
  | [] => true
  | [_] => true
  | p :: q :: rest => keyLt p q && keysStrict (q :: rest)

mutual
/-- Deterministic shape: no indefinite-length item anywhere, and every map's
keys strictly increasing in the bytewise order of their deterministic
encodings (§4.2.1; strictness excludes two keys with one encoding). -/
def isDeterministic : Item → Bool
  | .bytesIndef _ | .textIndef _ | .arrayIndef _ | .mapIndef _ => false
  | .array xs => isDeterministicList xs
  | .map kvs => keysStrict kvs && isDeterministicPairs kvs
  | .tag _ x => isDeterministic x
  | _ => true
def isDeterministicList : List Item → Bool
  | [] => true
  | x :: xs => isDeterministic x && isDeterministicList xs
def isDeterministicPairs : List (Item × Item) → Bool
  | [] => true
  | (k, v) :: kvs => isDeterministic k && isDeterministic v && isDeterministicPairs kvs
end

end Item

/-- The core deterministic encoding of an item (§4.2.1): preferred
serialization of its deterministic shape. -/
def encodeDeterministic (x : Item) : List UInt8 := encodePreferred x.normalise

/-- The strict decoder: `some x` exactly when `bs` is the core
deterministic encoding of the well-formed item `x`, `x` is in
deterministic shape, and all its text is valid UTF-8 (§4.2.1, §5.3.1). -/
def decodeDeterministic (bs : List UInt8) : Option Item :=
  match parseWellFormed bs with
  | none => none
  | some x =>
    if x.isDeterministic && x.textValid && encodeDeterministic x == bs then some x else none

/-! ## List views -/

namespace Item

theorem normaliseList_eq (xs : List Item) : normaliseList xs = xs.map normalise := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [normaliseList, ih]

theorem normalisePairs_eq (kvs : List (Item × Item)) :
    normalisePairs kvs = kvs.map fun kv => (normalise kv.1, normalise kv.2) := by
  induction kvs with
  | nil => rfl
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [normalisePairs, ih]

theorem isDeterministicList_iff (xs : List Item) :
    isDeterministicList xs = true ↔ ∀ x ∈ xs, isDeterministic x = true := by
  induction xs with
  | nil => simp [isDeterministicList]
  | cons x xs ih => simp [isDeterministicList, ih]

theorem isDeterministicPairs_iff (kvs : List (Item × Item)) :
    isDeterministicPairs kvs = true ↔
      ∀ kv ∈ kvs, isDeterministic kv.1 = true ∧ isDeterministic kv.2 = true := by
  induction kvs with
  | nil => simp [isDeterministicPairs]
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [isDeterministicPairs, ih, and_assoc]

theorem keysStrict_head_lt : ∀ (p : Item × Item) (l : List (Item × Item)),
    keysStrict (p :: l) = true → ∀ z ∈ l, keyLt p z = true
  | p, [], _ => by simp
  | p, q :: rest, h => by
    simp only [keysStrict, Bool.and_eq_true] at h
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact h.1
    · exact lexLt_trans h.1 (keysStrict_head_lt q rest h.2 z hz)

theorem keysStrict_tail : ∀ (p : Item × Item) (l : List (Item × Item)),
    keysStrict (p :: l) = true → keysStrict l = true
  | _, [], _ => rfl
  | _, _ :: _, h => by simp only [keysStrict, Bool.and_eq_true] at h; exact h.2

/-- Strictly increasing keys are sorted for `keyLt`. -/
theorem sortedBy_of_keysStrict : ∀ kvs : List (Item × Item), keysStrict kvs = true →
    SortedBy keyLt kvs
  | [], _ => trivial
  | p :: rest, h =>
    ⟨fun y hy => lexLt_asymm (keysStrict_head_lt p rest h y hy),
      sortedBy_of_keysStrict rest (keysStrict_tail p rest h)⟩

/-- Deterministic-shape items are fixed by `normalise`. -/
theorem normalise_of_isDeterministic {x : Item} (hx : x.isDeterministic = true) :
    x.normalise = x := by
  induction x using Item.rec' with
  | uint n => rfl
  | nint n => rfl
  | bytes p => rfl
  | text p => rfl
  | bytesIndef cs => simp [isDeterministic] at hx
  | textIndef cs => simp [isDeterministic] at hx
  | array xs ih =>
    simp only [isDeterministic, isDeterministicList_iff] at hx
    simp only [normalise, normaliseList_eq]
    congr 1
    exact (List.map_congr_left fun x hx' => ih x hx' (hx x hx')).trans (List.map_id _)
  | arrayIndef xs ih => simp [isDeterministic] at hx
  | map kvs ih =>
    simp only [isDeterministic, Bool.and_eq_true, isDeterministicPairs_iff] at hx
    obtain ⟨hs, hd⟩ := hx
    simp only [normalise, normalisePairs_eq]
    have hmap : (kvs.map fun kv => (normalise kv.1, normalise kv.2)) = kvs := by
      refine (List.map_congr_left fun kv hkv => ?_).trans (List.map_id _)
      rw [(ih kv hkv).1 (hd kv hkv).1, (ih kv hkv).2 (hd kv hkv).2]
      rfl
    rw [hmap, sortBy_of_sorted keyLt kvs (sortedBy_of_keysStrict kvs hs)]
  | mapIndef kvs ih => simp [isDeterministic] at hx
  | tag t x ih =>
    simp only [isDeterministic] at hx
    simp [normalise, ih hx]
  | simple v => rfl

end Item

/-! ## Round trips -/

/-- **Strict round trip (encode, then decode).** A well-formed item in
deterministic shape whose text is valid UTF-8 is decoded back from its
deterministic encoding. -/
theorem decodeDeterministic_encodeDeterministic {x : Item} (hwf : x.WF)
    (hdet : x.isDeterministic = true) (htext : x.textValid = true) :
    decodeDeterministic (encodeDeterministic x) = some x := by
  have hn := Item.normalise_of_isDeterministic hdet
  unfold decodeDeterministic encodeDeterministic
  rw [hn, parseWellFormed_encodePreferred hwf]
  simp [hdet, htext, hn]

/-- **Strict round trip (decode, then encode).** Whatever the strict decoder
accepts is re-encoded byte for byte, is in deterministic shape, is
well-formed, and has valid UTF-8 text. -/
theorem encodeDeterministic_of_decodeDeterministic {bs : List UInt8} {x : Item}
    (h : decodeDeterministic bs = some x) :
    encodeDeterministic x = bs ∧ x.isDeterministic = true ∧ x.textValid = true ∧ x.WF := by
  unfold decodeDeterministic at h
  split at h
  · simp at h
  · rename_i y hy
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨hc.2, hc.1.1, hc.1.2, parseWellFormed_WF hy⟩
    · simp at h

/-- The strict decoder accepts only well-formed input, and agrees with the
generic parser where it accepts. -/
theorem parseWellFormed_of_decodeDeterministic {bs : List UInt8} {x : Item}
    (h : decodeDeterministic bs = some x) : parseWellFormed bs = some x := by
  unfold decodeDeterministic at h
  split at h
  · simp at h
  · rename_i y hy
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact hy
    · simp at h

/-- `encodeDeterministic` factors through `normalise`, which is idempotent on
the encoding: `encodeDeterministic ∘ normalise = encodeDeterministic` holds
whenever deterministic shape is reached (see `Item.normalise_normalise`). -/
theorem encodeDeterministic_eq (x : Item) :
    encodeDeterministic x = encodePreferred x.normalise := rfl

end Cbor.Rfc8949
