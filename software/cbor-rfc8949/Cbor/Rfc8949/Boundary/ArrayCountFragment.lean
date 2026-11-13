import Std

/-!
Core-only grammar-fragment evidence for RFC 8949 issue #34.

This is not an implementation of `parseWellFormed`, nor a claimed theorem about
an implementation that does not yet exist. It formalizes the wire-level facts
that refute an unrestricted definite-producing, array-preserving transform:
an indefinite array has no element-count head; every definite array does.

RFC 8949 §3 allows inline arguments below 24, or unsigned big-endian arguments
of 1, 2, 4, or 8 bytes. §3.1 major type 4 makes that argument the element count.
§3.2.2 permits any finite sequence of items between 0x9f and the break 0xff.
The fragment below uses only integer-zero elements, so no float, text, tag,
map, validity, canonicalization, or equivalence choice affects the result.
-/

namespace CborLengthCounterexample

def beValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat * 256 ^ bs.length + beValue bs

theorem beValue_lt (bs : List UInt8) : beValue bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [beValue]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toBitVec.isLt
    have hmul := Nat.mul_le_mul_right (256 ^ bs.length) (show b.toNat ≤ 255 by omega)
    simp only [beValue, List.length_cons, Nat.pow_succ]
    omega

-- Complete list of argument forms for a definite major-type-4 head.
inductive DefiniteArrayHead : List UInt8 → Nat → Prop
  | inline (n : Nat) (hn : n < 24) :
      DefiniteArrayHead [UInt8.ofNat (0x80 + n)] n
  | one (bs : List UInt8) (h : bs.length = 1) :
      DefiniteArrayHead (0x98 :: bs) (beValue bs)
  | two (bs : List UInt8) (h : bs.length = 2) :
      DefiniteArrayHead (0x99 :: bs) (beValue bs)
  | four (bs : List UInt8) (h : bs.length = 4) :
      DefiniteArrayHead (0x9a :: bs) (beValue bs)
  | eight (bs : List UInt8) (h : bs.length = 8) :
      DefiniteArrayHead (0x9b :: bs) (beValue bs)

theorem definiteArrayHead_count_lt {head : List UInt8} {n : Nat}
    (h : DefiniteArrayHead head n) : n < 2 ^ 64 := by
  cases h with
  | inline n hn => omega
  | one bs h => have hb := beValue_lt bs; rw [h] at hb; omega
  | two bs h => have hb := beValue_lt bs; rw [h] at hb; omega
  | four bs h => have hb := beValue_lt bs; rw [h] at hb; omega
  | eight bs h => have hb := beValue_lt bs; rw [h] at hb; exact hb

-- Each 0x00 is a complete, preferred major-type-0 integer-zero item.
inductive ZeroSequence : List UInt8 → Nat → Prop
  | nil : ZeroSequence [] 0
  | cons {bs : List UInt8} {n : Nat} :
      ZeroSequence bs n → ZeroSequence (0x00 :: bs) (n + 1)

theorem zeroSequence_replicate (n : Nat) :
    ZeroSequence (List.replicate n 0x00) n := by
  induction n with
  | zero => exact .nil
  | succ n ih => simpa [List.replicate_succ] using ZeroSequence.cons ih

def WellFormedIndefiniteZeroArray (wire : List UInt8) (n : Nat) : Prop :=
  ∃ body, ZeroSequence body n ∧ wire = 0x9f :: (body ++ [0xff])

def counterexampleWire : List UInt8 :=
  0x9f :: (List.replicate (2 ^ 64) 0x00 ++ [0xff])

theorem counterexample_wellFormed :
    WellFormedIndefiniteZeroArray counterexampleWire (2 ^ 64) :=
  ⟨_, zeroSequence_replicate _, rfl⟩

theorem no_definite_head : ¬ ∃ head, DefiniteArrayHead head (2 ^ 64) := by
  rintro ⟨head, h⟩
  have hlt := definiteArrayHead_count_lt h
  exact Nat.lt_irrefl _ hlt

theorem unrestricted_deflation_counterexample :
    ∃ wire, WellFormedIndefiniteZeroArray wire (2 ^ 64) ∧
      ¬ ∃ head, DefiniteArrayHead head (2 ^ 64) :=
  ⟨counterexampleWire, counterexample_wellFormed, no_definite_head⟩

#print axioms beValue_lt
#print axioms definiteArrayHead_count_lt
#print axioms zeroSequence_replicate
#print axioms counterexample_wellFormed
#print axioms no_definite_head
#print axioms unrestricted_deflation_counterexample

end CborLengthCounterexample
