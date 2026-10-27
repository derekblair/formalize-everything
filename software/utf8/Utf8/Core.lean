import Utf8.Char

/-!
# Agreement with Lean core

Lean core does not define validity via Table 3-7: `ByteArray.IsValidUTF8`
is *defined* as being the `List.utf8Encode` of some list of characters,
and `ByteArray.validateUTF8` is core's executable validator, proved in
core to agree with that predicate (`ByteArray.validateUTF8_eq_true_iff`).

This file proves the exact agreement statements core's API supports:

* our `encodeCodepoint` is *definitionally* core's `String.utf8EncodeChar`
  (the same division/modulo formulas), hence `encodeAll` is core's
  `List.utf8Encode` up to the `List.toByteArray` packaging;
* consequently `Valid l ↔ ByteArray.IsValidUTF8 l.toByteArray`, with no
  gap: the independent Table 3-7 specification characterizes exactly
  the byte arrays core accepts;
* and therefore also `Valid l ↔ l.toByteArray.validateUTF8 = true`, and
  `Valid l` iff `l` is the byte content of some `String`.
-/

namespace Utf8

/-- Our shortest-form encoder is core's `String.utf8EncodeChar`:
the formulas are identical, so this is proved by `rfl`. -/
theorem encodeCodepoint_eq_core (c : Char) :
    encodeCodepoint c.val.toNat = String.utf8EncodeChar c :=
  rfl

/-- Hence `encodeAll` is the list underlying core's `List.utf8Encode`. -/
theorem encodeAll_eq_core (cs : List Char) :
    encodeAll cs = cs.flatMap String.utf8EncodeChar := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      rw [encodeAll_cons, ih, encodeCodepoint_eq_core]
      rfl

/-- `List.utf8Encode` is `encodeAll` packaged as a `ByteArray`. -/
theorem utf8Encode_eq_encodeAll (cs : List Char) :
    List.utf8Encode cs = (encodeAll cs).toByteArray := by
  show (cs.flatMap String.utf8EncodeChar).toByteArray =
    (encodeAll cs).toByteArray
  rw [← encodeAll_eq_core]

/-- **Agreement with core's validity predicate.** A byte list is
well-formed in the sense of Table 3-7 if and only if its `ByteArray`
is `ByteArray.IsValidUTF8` in core's sense. -/
theorem valid_iff_core {l : List UInt8} :
    Valid l ↔ ByteArray.IsValidUTF8 l.toByteArray := by
  constructor
  · intro hv
    obtain ⟨cs, -, henc⟩ := valid_iff_decode.1 hv
    refine ByteArray.IsValidUTF8.intro cs ?_
    rw [utf8Encode_eq_encodeAll, henc]
  · intro hv
    obtain ⟨cs, hcs⟩ := hv
    have henc : encodeAll cs = l := by
      rw [utf8Encode_eq_encodeAll] at hcs
      exact (List.toByteArray_inj.1 hcs).symm
    exact valid_iff_decode.2 ⟨cs, by rw [← henc]; exact decode_encodeAll cs,
      henc⟩

/-- **Agreement with core's executable validator.** -/
theorem valid_iff_validate {l : List UInt8} :
    Valid l ↔ l.toByteArray.validateUTF8 = true :=
  valid_iff_core.trans ByteArray.validateUTF8_eq_true_iff.symm

/-- **Agreement with `String`.** A byte list is well-formed if and
only if it is the byte content of some string. -/
theorem valid_iff_exists_string {l : List UInt8} :
    Valid l ↔ ∃ s : String, s.toByteArray = l.toByteArray := by
  constructor
  · intro hv
    exact ⟨String.fromUTF8 _ (valid_iff_core.1 hv), rfl⟩
  · rintro ⟨s, hs⟩
    apply valid_iff_core.2
    rw [← hs]
    exact s.isValidUTF8

end Utf8
