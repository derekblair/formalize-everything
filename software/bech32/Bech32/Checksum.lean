import Std

/-!
The BIP-173/BIP-350 checksum state machine. The state has exactly 30 bits,
so shifting left by five already discards the high five bits, as does the
reference expression `(chk & 0x1ffffff) << 5`. Data symbols have exactly five
bits; the encoder never takes unrestricted integers and reduces them modulo 32.
-/

namespace Bech32

abbrev Word := BitVec 5

inductive Variant where
  | bech32
  | bech32m
  deriving DecidableEq, Repr, BEq

def Variant.constant : Variant → BitVec 30
  | .bech32 => 1
  | .bech32m => 0x2bc830a3

/-- One iteration of the reference polynomial remainder recurrence. -/
def polymodStep (state : BitVec 30) (value : Word) : BitVec 30 :=
  (state <<< 5) ^^^ value.setWidth 30 ^^^
  (if state.getLsbD 25 then 0x3b6a57b2 else 0) ^^^
  (if state.getLsbD 26 then 0x26508e6d else 0) ^^^
  (if state.getLsbD 27 then 0x1ea119fa else 0) ^^^
  (if state.getLsbD 28 then 0x3d4233dd else 0) ^^^
  (if state.getLsbD 29 then 0x2a1462b3 else 0)

def polymod (values : List Word) : BitVec 30 :=
  values.foldl polymodStep 1

/-- On printable ASCII HRPs these are exactly the high and low five bits. -/
def hrpExpand (hrp : List Char) : List Word :=
  hrp.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5)) ++ [0] ++
    hrp.map (fun c => BitVec.ofNat 5 (c.toNat &&& 31))

/-- No high or low HRP bits are lost on the BIPs' permitted ASCII domain. -/
theorem hrpExpand_toNat (hrp : List Char) (h : ∀ c ∈ hrp, c.toNat ≤ 126) :
    (hrpExpand hrp).map BitVec.toNat =
      hrp.map (fun c => c.toNat >>> 5) ++ [0] ++
        hrp.map (fun c => c.toNat &&& 31) := by
  have hh : hrp.map (fun c => (BitVec.ofNat 5 (c.toNat >>> 5)).toNat) =
      hrp.map (fun c => c.toNat >>> 5) := by
    apply List.map_congr_left
    intro c hc
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have hc' := h c hc
    simp only [Nat.shiftRight_eq_div_pow]
    omega
  have hl : hrp.map (fun c => (BitVec.ofNat 5 (c.toNat &&& 31)).toNat) =
      hrp.map (fun c => c.toNat &&& 31) := by
    apply List.map_congr_left
    intro c _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.and_lt_two_pow c.toNat (by decide : 31 < 2^5)
  simp only [hrpExpand, List.map_append, List.map_map, List.map_cons, List.map_nil,
    Function.comp_def]
  rw [hh, hl]
  rfl

/-- The six five-bit digits of a 30-bit checksum, most significant first. -/
def checksumWords (state : BitVec 30) : List Word :=
  [state.extractLsb' 25 5, state.extractLsb' 20 5,
   state.extractLsb' 15 5, state.extractLsb' 10 5,
   state.extractLsb' 5 5, state.extractLsb' 0 5]

def createChecksum (variant : Variant) (hrp : List Char) (data : List Word) : List Word :=
  checksumWords (polymod (hrpExpand hrp ++ data ++ [0, 0, 0, 0, 0, 0]) ^^^ variant.constant)

def verifyChecksum (variant : Variant) (hrp : List Char) (data : List Word) : Bool :=
  polymod (hrpExpand hrp ++ data) == variant.constant

@[simp] theorem length_checksumWords (state : BitVec 30) :
    (checksumWords state).length = 6 := rfl

@[simp] theorem length_createChecksum (v : Variant) (hrp : List Char) (data : List Word) :
    (createChecksum v hrp data).length = 6 := rfl

private theorem select_xor (a b : Bool) (g : BitVec 30) :
    (if a ^^ b then g else 0) = (if a then g else 0) ^^^ (if b then g else 0) := by
  cases a <;> cases b <;> simp

/-- The update is linear over bitwise XOR in its state and input symbol. -/
theorem polymodStep_xor (s t : BitVec 30) (v w : Word) :
    polymodStep (s ^^^ t) (v ^^^ w) = polymodStep s v ^^^ polymodStep t w := by
  simp only [polymodStep, BitVec.shiftLeft_xor_distrib, BitVec.setWidth_xor,
    BitVec.getLsbD_xor, select_xor]
  ac_rfl

@[simp] theorem polymodStep_zero : polymodStep 0 0 = 0 := rfl

/-- Feeding six symbols into a zero state simply packs their bits. -/
theorem fold_checksumWords_zero (s : BitVec 30) :
    (checksumWords s).foldl polymodStep 0 = s := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨
      i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 := by omega
  rcases cases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [checksumWords, polymodStep]

/-- Folding two equally long streams respects pointwise XOR. -/
theorem foldl_polymodStep_xor (xs ys : List Word) (s t : BitVec 30)
    (h : xs.length = ys.length) :
    (List.zipWith (· ^^^ ·) xs ys).foldl polymodStep (s ^^^ t) =
      xs.foldl polymodStep s ^^^ ys.foldl polymodStep t := by
  induction xs generalizing ys s t with
  | nil =>
      have : ys = [] := List.eq_nil_of_length_eq_zero h.symm
      subst ys
      rfl
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          simp only [List.zipWith_cons_cons, List.foldl_cons, polymodStep_xor]
          exact ih ys (polymodStep s x) (polymodStep t y) h

/-- The six checksum symbols contribute their packed value to the final state. -/
theorem fold_checksumWords (s q : BitVec 30) :
    (checksumWords q).foldl polymodStep s =
      ([0, 0, 0, 0, 0, 0] : List Word).foldl polymodStep s ^^^ q := by
  have h := foldl_polymodStep_xor [0, 0, 0, 0, 0, 0] (checksumWords q) s 0 rfl
  rw [fold_checksumWords_zero] at h
  simpa [checksumWords] using h

/-- Appending the generated checksum yields the selected BIP residue. -/
theorem verifyChecksum_createChecksum (variant : Variant) (hrp : List Char)
    (data : List Word) :
    verifyChecksum variant hrp (data ++ createChecksum variant hrp data) = true := by
  simp only [verifyChecksum, createChecksum, polymod, List.foldl_append]
  rw [fold_checksumWords, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  simp

/-- Six five-bit values can be recovered from their zero-state fold. -/
theorem checksumWords_fold_six (a b c d e f : Word) :
    checksumWords ([a, b, c, d, e, f].foldl polymodStep 0) = [a, b, c, d, e, f] := by
  simp only [checksumWords, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl
    all_goals simp [polymodStep]

/-- `checksumWords` inverts the zero-state fold of every six-symbol suffix. -/
theorem checksumWords_fold_of_length (xs : List Word) (h : xs.length = 6) :
    checksumWords (xs.foldl polymodStep 0) = xs := by
  obtain ⟨a, xs, rfl⟩ := List.exists_cons_of_length_pos (l := xs) (by omega)
  simp only [List.length_cons] at h
  obtain ⟨b, xs, rfl⟩ := List.exists_cons_of_length_pos (l := xs) (by omega)
  simp only [List.length_cons] at h
  obtain ⟨c, xs, rfl⟩ := List.exists_cons_of_length_pos (l := xs) (by omega)
  simp only [List.length_cons] at h
  obtain ⟨d, xs, rfl⟩ := List.exists_cons_of_length_pos (l := xs) (by omega)
  simp only [List.length_cons] at h
  obtain ⟨e, xs, rfl⟩ := List.exists_cons_of_length_pos (l := xs) (by omega)
  simp only [List.length_cons] at h
  obtain ⟨f, xs, rfl⟩ := List.exists_cons_of_length_pos (l := xs) (by omega)
  simp only [List.length_cons] at h
  have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst xs
  exact checksumWords_fold_six a b c d e f

/-- A six-symbol suffix acts by XOR with its packed value. -/
theorem fold_six (s : BitVec 30) (xs : List Word) (h : xs.length = 6) :
    xs.foldl polymodStep s =
      ([0, 0, 0, 0, 0, 0] : List Word).foldl polymodStep s ^^^
        xs.foldl polymodStep 0 := by
  calc
    xs.foldl polymodStep s = (checksumWords (xs.foldl polymodStep 0)).foldl polymodStep s :=
      congrArg (List.foldl polymodStep s) (checksumWords_fold_of_length xs h).symm
    _ = _ := fold_checksumWords s _

/-- For a fixed prefix state, distinct six-symbol suffixes give distinct residues. -/
theorem fold_six_injective (s : BitVec 30) (xs ys : List Word)
    (hx : xs.length = 6) (hy : ys.length = 6)
    (h : xs.foldl polymodStep s = ys.foldl polymodStep s) : xs = ys := by
  rw [fold_six s xs hx, fold_six s ys hy] at h
  have heq := (BitVec.xor_right_inj _).mp h
  have hwords := congrArg checksumWords heq
  simpa only [checksumWords_fold_of_length xs hx, checksumWords_fold_of_length ys hy] using hwords

/-- Exactly one six-symbol suffix verifies: the one returned by `createChecksum`. -/
theorem verifyChecksum_iff_createChecksum (variant : Variant) (hrp : List Char)
    (data suffix : List Word) (hlen : suffix.length = 6) :
    verifyChecksum variant hrp (data ++ suffix) = true ↔
      suffix = createChecksum variant hrp data := by
  constructor
  · intro h
    have hcreated := verifyChecksum_createChecksum variant hrp data
    simp only [verifyChecksum, beq_iff_eq] at h hcreated
    have heq := h.trans hcreated.symm
    simp only [polymod, List.foldl_append] at heq
    exact fold_six_injective _ _ _ hlen (length_createChecksum ..) heq
  · intro h
    subst suffix
    exact verifyChecksum_createChecksum variant hrp data

end Bech32
