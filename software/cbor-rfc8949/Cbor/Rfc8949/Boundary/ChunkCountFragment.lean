import Std

/-!
Grammar-fragment evidence for RFC 8949 issue #34, amended deliverable 2.

The amendment bounds an indefinite aggregate's element/chunk COUNT by 2^64.
For strings this does not bound the concatenated payload's BYTE LENGTH.
Two definite byte-string chunks of length 2^63 satisfy the count premise,
but their concatenation has length 2^64 and has no definite encoding.

This file does not implement `parseWellFormed` or `deflateIndefinite` and
does not claim a theorem about implementations of those functions. It
formalizes the complete definite byte-string head grammar, definite chunks,
the indefinite byte-string concatenation grammar, and an explicit symbolic
counterexample. No enormous list is evaluated or allocated by these proofs.

RFC 8949 section 3 permits definite arguments inline or in 1, 2, 4, or 8
bytes. Section 3.1 makes a byte-string argument its payload byte length.
Section 3.2.3 concatenates the payloads of definite byte-string chunks.
-/

namespace CborChunkCountCounterexample

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

-- Every allowed definite major-type-2 head, including non-preferred heads.
inductive DefiniteByteStringHead : List UInt8 → Nat → Prop
  | inline (n : Nat) (hn : n < 24) :
      DefiniteByteStringHead [UInt8.ofNat (0x40 + n)] n
  | one (bs : List UInt8) (h : bs.length = 1) :
      DefiniteByteStringHead (0x58 :: bs) (beValue bs)
  | two (bs : List UInt8) (h : bs.length = 2) :
      DefiniteByteStringHead (0x59 :: bs) (beValue bs)
  | four (bs : List UInt8) (h : bs.length = 4) :
      DefiniteByteStringHead (0x5a :: bs) (beValue bs)
  | eight (bs : List UInt8) (h : bs.length = 8) :
      DefiniteByteStringHead (0x5b :: bs) (beValue bs)

theorem definiteByteStringHead_length_lt {head : List UInt8} {n : Nat}
    (h : DefiniteByteStringHead head n) : n < 2 ^ 64 := by
  cases h with
  | inline n hn => omega
  | one bs h => have hb := beValue_lt bs; rw [h] at hb; omega
  | two bs h => have hb := beValue_lt bs; rw [h] at hb; omega
  | four bs h => have hb := beValue_lt bs; rw [h] at hb; omega
  | eight bs h => have hb := beValue_lt bs; rw [h] at hb; exact hb

-- A complete definite byte string has exactly the advertised payload length.
def DefiniteByteString (wire payload : List UInt8) : Prop :=
  ∃ head, DefiniteByteStringHead head payload.length ∧ wire = head ++ payload

theorem definiteByteString_length_lt {wire payload : List UInt8}
    (h : DefiniteByteString wire payload) : payload.length < 2 ^ 64 := by
  obtain ⟨head, hh, _⟩ := h
  exact definiteByteStringHead_length_lt hh

-- Chunks must themselves be definite byte strings, never nested indefinite
-- strings. The third index counts chunks; the second concatenates payloads.
inductive ChunkSequence : List UInt8 → List UInt8 → Nat → Prop
  | nil : ChunkSequence [] [] 0
  | cons {chunk rest payload tail : List UInt8} {n : Nat} :
      DefiniteByteString chunk payload → ChunkSequence rest tail n →
      ChunkSequence (chunk ++ rest) (payload ++ tail) (n + 1)

def IndefiniteByteString (wire payload : List UInt8) (chunkCount : Nat) : Prop :=
  ∃ body, ChunkSequence body payload chunkCount ∧ wire = 0x5f :: (body ++ [0xff])

-- In this fragment the outer string is the only indefinite aggregate.
-- Consequently this is exactly the amended per-indefinite-aggregate
-- chunk-count premise for these wires, with no omitted nested aggregates.
def ChunkCountBound (wire payload : List UInt8) : Prop :=
  ∃ n, IndefiniteByteString wire payload n ∧ n < 2 ^ 64

def chunkPayload : List UInt8 := List.replicate (2 ^ 63) 0x00

def chunkHead : List UInt8 := [0x5b, 0x80, 0, 0, 0, 0, 0, 0, 0]

def chunkWire : List UInt8 := chunkHead ++ chunkPayload

def joinedPayload : List UInt8 := chunkPayload ++ chunkPayload

def counterexampleWire : List UInt8 :=
  0x5f :: ((chunkWire ++ chunkWire) ++ [0xff])

theorem chunkPayload_length : chunkPayload.length = 2 ^ 63 := by
  simp only [chunkPayload, List.length_replicate]

theorem chunkHead_encodes_length : DefiniteByteStringHead chunkHead (2 ^ 63) := by
  have h := DefiniteByteStringHead.eight [0x80, 0, 0, 0, 0, 0, 0, 0] rfl
  exact h

theorem chunk_wellFormed : DefiniteByteString chunkWire chunkPayload := by
  refine ⟨chunkHead, ?_, rfl⟩
  rw [chunkPayload_length]
  exact chunkHead_encodes_length

theorem two_chunks_wellFormed :
    ChunkSequence (chunkWire ++ chunkWire) joinedPayload 2 := by
  have h := ChunkSequence.cons chunk_wellFormed
    (ChunkSequence.cons chunk_wellFormed ChunkSequence.nil)
  simpa only [List.append_nil, joinedPayload] using h

theorem counterexample_wellFormed :
    IndefiniteByteString counterexampleWire joinedPayload 2 :=
  ⟨chunkWire ++ chunkWire, two_chunks_wellFormed, rfl⟩

theorem counterexample_satisfies_chunkCountBound :
    ChunkCountBound counterexampleWire joinedPayload :=
  ⟨2, counterexample_wellFormed, by decide⟩

theorem joinedPayload_length : joinedPayload.length = 2 ^ 64 := by
  simp only [joinedPayload, List.length_append, chunkPayload_length]

theorem no_definite_preserving_payload :
    ¬ ∃ wire, DefiniteByteString wire joinedPayload := by
  rintro ⟨wire, h⟩
  have hlt := definiteByteString_length_lt h
  rw [joinedPayload_length] at hlt
  exact Nat.lt_irrefl _ hlt

theorem chunk_count_bound_deflation_counterexample :
    ∃ wire payload,
      ChunkCountBound wire payload ∧ ¬ ∃ output, DefiniteByteString output payload :=
  ⟨counterexampleWire, joinedPayload,
    counterexample_satisfies_chunkCountBound, no_definite_preserving_payload⟩

theorem chunk_count_bound_insufficient :
    ¬ (∀ wire payload, ChunkCountBound wire payload →
      ∃ output, DefiniteByteString output payload) := by
  intro h
  exact no_definite_preserving_payload
    (h counterexampleWire joinedPayload counterexample_satisfies_chunkCountBound)

#print axioms beValue_lt
#print axioms definiteByteStringHead_length_lt
#print axioms definiteByteString_length_lt
#print axioms chunkPayload_length
#print axioms chunkHead_encodes_length
#print axioms chunk_wellFormed
#print axioms two_chunks_wellFormed
#print axioms counterexample_wellFormed
#print axioms counterexample_satisfies_chunkCountBound
#print axioms joinedPayload_length
#print axioms no_definite_preserving_payload
#print axioms chunk_count_bound_deflation_counterexample
#print axioms chunk_count_bound_insufficient

end CborChunkCountCounterexample
