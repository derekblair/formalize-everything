import Bech32.Checksum

/-!
The generic Bech32/Bech32m text layer. The separator search walks from the right,
so an HRP may itself contain `1`. A decoder accepts either uniform case and
returns the canonical lowercase HRP. Encoders always emit lowercase.
-/

namespace Bech32

/-- The BIP-173 alphabet, in value order. -/
def charset : List Char := "qpzry9x8gf2tvdw0s3jn54khce6mua7l".toList

/-- An input symbol already has exactly five bits. -/
def charOfWord (w : Word) : Char := charset[w.toNat]'w.isLt

/-- Exact inverse lookup; characters outside the alphabet fail. -/
def charToWord (c : Char) : Option Word :=
  match charset.idxOf? c with
  | none => none
  | some n => if h : n < 32 then some ⟨⟨n, h⟩⟩ else none

@[simp] theorem charToWord_charOfWord (w : Word) :
    charToWord (charOfWord w) = some w := by
  exact (by decide : ∀ w : Word, charToWord (charOfWord w) = some w) w

/-- Successful inverse lookup returns precisely the character that was supplied. -/
theorem charOfWord_charToWord {c : Char} {w : Word} (h : charToWord c = some w) :
    charOfWord w = c := by
  unfold charToWord at h
  cases hidx : charset.idxOf? c with
  | none => simp [hidx] at h
  | some n =>
    simp only [hidx] at h
    split at h
    next hn =>
      have hw := Option.some.inj h
      subst w
      exact (List.idxOf?_eq_some_iff.mp hidx).choose_spec.1
    next hn => simp at h

/-- Printable US-ASCII, inclusive of both BIP endpoints. -/
def printable (c : Char) : Bool := 33 ≤ c.toNat && c.toNat ≤ 126

@[simp] theorem charOfWord_printable (w : Word) : printable (charOfWord w) = true := by
  exact (by decide : ∀ w : Word, printable (charOfWord w) = true) w

@[simp] theorem charOfWord_not_upper (w : Word) : (charOfWord w).isUpper = false := by
  exact (by decide : ∀ w : Word, (charOfWord w).isUpper = false) w

@[simp] theorem charOfWord_not_separator (w : Word) : (charOfWord w == '1') = false := by
  exact (by decide : ∀ w : Word, (charOfWord w == '1') = false) w

/-- Split at the last `1`, preserving any earlier occurrences in the HRP. -/
def splitLast : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
    match splitLast cs with
    | some (hrp, data) => some (c :: hrp, data)
    | none => if c == '1' then some ([], cs) else none

/-- List form of the canonical lowercase encoder. Validity is stated separately. -/
def encodeChars (variant : Variant) (hrp : List Char) (data : List Word) : List Char :=
  let lower := hrp.map Char.toLower
  lower ++ '1' :: (data ++ createChecksum variant lower data).map charOfWord

/-- Generic decoder, including all textual validity checks and the selected checksum. -/
def decodeChars (variant : Variant) (s : List Char) : Option (List Char × List Word) :=
  if s.length > 90 || !(s.all printable) || (s.any Char.isUpper && s.any Char.isLower) then
    none
  else
    match splitLast (s.map Char.toLower) with
    | none => none
    | some (hrp, raw) =>
      if hrp.isEmpty || raw.length < 6 then none
      else do
        let words ← raw.mapM charToWord
        if verifyChecksum variant hrp words then
          some (hrp, words.take (words.length - 6))
        else none

/-- Canonical BIP encoder. Callers use `ValidInput` to enforce the BIP length/HRP domain. -/
def encode (variant : Variant) (hrp : String) (data : List Word) : String :=
  String.ofList (encodeChars variant hrp.toList data)

/-- Decode as the explicitly selected Bech32 variant. -/
def decode (variant : Variant) (s : String) : Option (String × List Word) :=
  (decodeChars variant s.toList).map (fun (hrp, data) => (String.ofList hrp, data))

/-- Try the two disjoint checksum constants, as in BIP-350's combined decoder. -/
def decodeAny (s : String) : Option (Variant × String × List Word) :=
  match decode .bech32 s with
  | some (hrp, data) => some (.bech32, hrp, data)
  | none => (decode .bech32m s).map (fun (hrp, data) => (.bech32m, hrp, data))

/-- Valid canonical encoder inputs: nonempty printable lowercase HRP and total length at most 90.
The data type itself enforces the five-bit condition. HRP length at most 83 follows. -/
def ValidInputChars (hrp : List Char) (data : List Word) : Prop :=
  hrp ≠ [] ∧ hrp.all printable = true ∧ hrp.any Char.isUpper = false ∧
    hrp.length + data.length + 7 ≤ 90

def ValidInput (hrp : String) (data : List Word) : Prop :=
  ValidInputChars hrp.toList data

private theorem toLower_eq_self_of_not_upper {c : Char} (h : c.isUpper = false) :
    c.toLower = c := by
  simp only [Char.isUpper, decide_eq_false_iff_not] at h
  unfold Char.toLower
  rw [dite_eq_right h]

private theorem map_toLower_of_not_upper {cs : List Char} (h : cs.any Char.isUpper = false) :
    cs.map Char.toLower = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    simp [toLower_eq_self_of_not_upper h.1, ih h.2]

@[simp] theorem map_charToWord (data : List Word) :
    (data.map charOfWord).mapM charToWord = some data := by
  induction data with
  | nil => rfl
  | cons w ws ih => simp [ih]

@[simp] theorem splitLast_data (data : List Word) :
    splitLast (data.map charOfWord) = none := by
  induction data with
  | nil => rfl
  | cons w ws ih => simp [splitLast, ih]

@[simp] theorem splitLast_encoded (hrp : List Char) (data : List Word) :
    splitLast (hrp ++ '1' :: data.map charOfWord) = some (hrp, data.map charOfWord) := by
  induction hrp with
  | nil => simp [splitLast]
  | cons c cs ih => simp [splitLast, ih]

@[simp] theorem data_printable (data : List Word) :
    (data.map charOfWord).all printable = true := by simp

@[simp] theorem data_not_upper (data : List Word) :
    (data.map charOfWord).any Char.isUpper = false := by simp

/-- Parsing is independent of checksum algebra: any correctly checksummed text round-trips. -/
theorem decodeChars_assembled (variant : Variant) (hrp : List Char) (data suffix : List Word)
    (hvalid : ValidInputChars hrp data) (hlen : suffix.length = 6)
    (hcheck : verifyChecksum variant hrp (data ++ suffix) = true) :
    decodeChars variant (hrp ++ '1' :: (data ++ suffix).map charOfWord) = some (hrp, data) := by
  rcases hvalid with ⟨hnonempty, hprint, hupper, hlength⟩
  have hstringupper : (hrp ++ '1' :: (data ++ suffix).map charOfWord).any Char.isUpper = false := by
    simp only [List.any_append, List.any_cons, hupper, data_not_upper]
    decide
  have hstringprint : (hrp ++ '1' :: (data ++ suffix).map charOfWord).all printable = true := by
    simp only [List.all_append, List.all_cons, hprint, data_printable]
    decide
  have hstringlength : (hrp ++ '1' :: (data ++ suffix).map charOfWord).length ≤ 90 := by
    simp only [List.length_append, List.length_cons, List.length_map, hlen]
    omega
  have hrawlength : ¬ (data ++ suffix).length < 6 := by
    simp only [List.length_append, hlen]
    omega
  unfold decodeChars
  simp only [hstringprint, hstringupper, Bool.false_and, Bool.not_true, Bool.or_false]
  rw [ite_eq_right (by simpa using Nat.not_lt.mpr hstringlength)]
  rw [map_toLower_of_not_upper hstringupper, splitLast_encoded]
  simp only [List.length_map]
  rw [ite_eq_right (by simpa [List.isEmpty_iff, hnonempty] using hrawlength)]
  rw [map_charToWord]
  simp [hcheck, hlen]

/-- Full text round trip for arbitrary valid canonical inputs and either checksum variant. -/
theorem decodeChars_encodeChars (variant : Variant) (hrp : List Char) (data : List Word)
    (hvalid : ValidInputChars hrp data) :
    decodeChars variant (encodeChars variant hrp data) = some (hrp, data) := by
  unfold encodeChars
  rw [map_toLower_of_not_upper hvalid.2.2.1]
  exact decodeChars_assembled variant hrp data (createChecksum variant hrp data)
    hvalid (length_createChecksum ..) (verifyChecksum_createChecksum ..)

/-- String-level identity theorem, uniformly covering both BIP checksum constants. -/
theorem decode_encode (variant : Variant) (hrp : String) (data : List Word)
    (hvalid : ValidInput hrp data) :
    decode variant (encode variant hrp data) = some (hrp, data) := by
  simp only [decode, encode, String.toList_ofList]
  rw [decodeChars_encodeChars variant hrp.toList data hvalid]
  simp

/-- BIP-173's canonical encoder is inverted by its decoder. -/
theorem decode_encode_bech32 (hrp : String) (data : List Word)
    (hvalid : ValidInput hrp data) :
    decode .bech32 (encode .bech32 hrp data) = some (hrp, data) :=
  decode_encode .bech32 hrp data hvalid

/-- BIP-350's canonical encoder is inverted by its decoder. -/
theorem decode_encode_bech32m (hrp : String) (data : List Word)
    (hvalid : ValidInput hrp data) :
    decode .bech32m (encode .bech32m hrp data) = some (hrp, data) :=
  decode_encode .bech32m hrp data hvalid

private theorem lower_printable {c : Char} (h : printable c = true) :
    printable c.toLower = true ∧ c.toLower.isUpper = false := by
  have hlt : c.toNat < 128 := by
    simp only [printable, Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  have finite : ∀ n : Fin 128, printable (Char.ofNat n.val) = true →
      printable (Char.ofNat n.val).toLower = true ∧
      (Char.ofNat n.val).toLower.isUpper = false := by decide
  simpa using finite ⟨c.toNat, hlt⟩ (by simpa using h)

/-- Canonicalization preserves every HRP validity condition. -/
theorem validInputChars_lower (hrp : List Char) (data : List Word)
    (hne : hrp ≠ []) (hprint : hrp.all printable = true)
    (hlen : hrp.length + data.length + 7 ≤ 90) :
    ValidInputChars (hrp.map Char.toLower) data := by
  refine ⟨by simpa using hne, ?_, ?_, by simpa using hlen⟩
  · simp only [List.all_eq_true] at hprint ⊢
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (lower_printable (hprint d hd)).1
  · simp only [List.any_eq_false]
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    simpa using (lower_printable (List.all_eq_true.mp hprint d hd)).2

/-- Round trip without a case restriction on the input HRP: decoding returns its lowercase form. -/
theorem decode_encode_normalized (variant : Variant) (hrp : String) (data : List Word)
    (hne : hrp.toList ≠ []) (hprint : hrp.toList.all printable = true)
    (hlen : hrp.toList.length + data.length + 7 ≤ 90) :
    decode variant (encode variant hrp data) =
      some (String.ofList (hrp.toList.map Char.toLower), data) := by
  have hvalid := validInputChars_lower hrp.toList data hne hprint hlen
  simp only [decode, encode, String.toList_ofList, encodeChars]
  rw [decodeChars_assembled variant (hrp.toList.map Char.toLower) data
    (createChecksum variant (hrp.toList.map Char.toLower) data) hvalid
    (length_createChecksum ..) (verifyChecksum_createChecksum ..)]
  rfl

/-- The output length is exactly HRP plus separator, payload and six checksum symbols. -/
theorem length_encode (variant : Variant) (hrp : String) (data : List Word) :
    (encode variant hrp data).toList.length = hrp.toList.length + data.length + 7 := by
  simp [encode, encodeChars]
  omega

/-- The total bound implies the BIP's maximum HRP length of 83. -/
theorem ValidInput.hrp_length_le_83 {hrp : String} {data : List Word}
    (h : ValidInput hrp data) : hrp.toList.length ≤ 83 := by
  have := h.2.2.2
  omega

end Bech32
