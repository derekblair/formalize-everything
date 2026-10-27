import Sha256Bridge.Upstream
import Hash.Sha256

/-!
Byte-level alignment of the two pinned implementations. The `Upstream` names
refer to the original private definitions in `LeanSha256.Core`.
-/

namespace Sha256Bridge

open Hash.Sha256

private theorem masked_toUInt8 (n : Nat) :
    Nat.toUInt8 (n &&& 255) = UInt8.ofNat n := by
  change UInt8.ofNat (n &&& (2^8 - 1)) = UInt8.ofNat n
  rw [Nat.and_two_pow_sub_one_eq_mod]
  apply UInt8.toNat.inj
  simp

/-- The original eight-byte length encoder agrees with the specification's
byte encoder, including its modulo-`2^64` behavior. -/
theorem uint64ToBytesBE_toList (n : Nat) :
    (Upstream.uint64ToBytesBE n).data.toList = Impl.lengthBytes n := by
  change [Nat.toUInt8 ((n >>> 56) &&& 255),
    Nat.toUInt8 ((n >>> 48) &&& 255), Nat.toUInt8 ((n >>> 40) &&& 255),
    Nat.toUInt8 ((n >>> 32) &&& 255), Nat.toUInt8 ((n >>> 24) &&& 255),
    Nat.toUInt8 ((n >>> 16) &&& 255), Nat.toUInt8 ((n >>> 8) &&& 255),
    Nat.toUInt8 (n &&& 255)] = _
  simp only [masked_toUInt8, Impl.lengthBytes]

private theorem padding_zero_count (n : Nat) :
    (if (n + 1) % 64 ≤ 56 then 56 - (n + 1) % 64
      else 56 + 64 - (n + 1) % 64) = (119 - n % 64) % 64 := by
  split <;> omega

/-- Padding agrees as a byte array on every input, with no length bound. -/
theorem pad_eq_fast (input : ByteArray) :
    Upstream.pad input = Fast.padBytes input := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  change ((input.push 128 ++ ByteArray.mk
    (Array.replicate (if (input.push 128).size % 64 ≤ 56
      then 56 - (input.push 128).size % 64
      else 56 + 64 - (input.push 128).size % 64) 0)) ++
    Upstream.uint64ToBytesBE (input.size * 8)).data.toList = _
  simp only [ByteArray.toList_data_append, ByteArray.data_push,
    Array.toList_push, Array.toList_replicate, ByteArray.size_push,
    uint64ToBytesBE_toList, padding_zero_count,
    Fast.padBytes, Fast.padSuffix, List.toList_data_toByteArray]
  simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.mul_comm]

/-- Four original byte reads have the same big-endian word interpretation. -/
theorem bytesToWordBE_eq_fast (b0 b1 b2 b3 : UInt8) :
    Upstream.bytesToWordBE b0 b1 b2 b3 =
      (b0.toUInt32 <<< 24) ||| ((b1.toUInt32 <<< 16) |||
        ((b2.toUInt32 <<< 8) ||| b3.toUInt32)) := by
  change ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16)) |||
    (b2.toUInt32 <<< 8) ||| b3.toUInt32 = _
  simp only [UInt32.or_assoc]

/-- Parsing a complete 64-byte block agrees with the verified native layer. -/
theorem extractBlock_eq_fast (padded : ByteArray) (blockIdx : Nat)
    (h : (blockIdx + 1) * 64 ≤ padded.size) :
    Upstream.extractBlock padded blockIdx = (Fast.wordsAt padded (64 * blockIdx)).toArray := by
  change (Array.ofFn fun j : Fin 16 =>
    Upstream.bytesToWordBE padded[blockIdx * 64 + j.val * 4]!
      padded[blockIdx * 64 + j.val * 4 + 1]!
      padded[blockIdx * 64 + j.val * 4 + 2]!
      padded[blockIdx * 64 + j.val * 4 + 3]!) = _
  apply Array.ext
  · simp
  · intro i hi hi'
    have hi16 : i < 16 := by simpa using hi
    have h0 : blockIdx * 64 + i * 4 < padded.size := by omega
    have h1 : blockIdx * 64 + i * 4 + 1 < padded.size := by omega
    have h2 : blockIdx * 64 + i * 4 + 2 < padded.size := by omega
    have h3 : blockIdx * 64 + i * 4 + 3 < padded.size := by omega
    simp only [Array.getElem_ofFn, bytesToWordBE_eq_fast,
      getElem!_pos padded (blockIdx * 64 + i * 4) h0, getElem!_pos padded (blockIdx * 64 + i * 4 + 1) h1,
      getElem!_pos padded (blockIdx * 64 + i * 4 + 2) h2, getElem!_pos padded (blockIdx * 64 + i * 4 + 3) h3]
    change _ = (Fast.wordsAt padded (64 * blockIdx))[i]
    rw [Fast.wordsAt, Vec.getElem_ofFn, Fast.wordAt]
    simp only [Fast.byteAt, Nat.mul_comm 64 blockIdx, Nat.mul_comm 4 i,
      dite_eq_left h0, dite_eq_left h1, dite_eq_left h2, dite_eq_left h3]

/-- The original word serializer agrees with the verified native layer. -/
theorem wordToBytesBE_toList (w : UInt32) :
    (Upstream.wordToBytesBE w).data.toList = Fast.bytesOfWord w := rfl

private theorem pack_list (xs : List UInt32) (acc : ByteArray) :
    ((xs.foldl (fun a w => a ++ Upstream.wordToBytesBE w) acc).data.toList) =
      acc.data.toList ++ xs.flatMap Fast.bytesOfWord := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, ByteArray.toList_data_append,
      wordToBytesBE_toList, List.flatMap_cons, List.append_assoc]

/-- Serializing the eight-word final state agrees exactly. -/
theorem packState_eq_fast (state : Fast.St) :
    Upstream.packState state.toArray = Fast.squeeze state := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  change ((state.toArray.foldl (fun acc w => acc ++ Upstream.wordToBytesBE w)
    ByteArray.empty).data.toList) = _
  rw [← Array.foldl_toList, pack_list]
  simp only [Fast.squeeze, List.toList_data_toByteArray]
  change state.toArray.toList.flatMap Fast.bytesOfWord = _
  have hs : (List.finRange 8).map (fun i => state[i]) = state.toArray.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [← hs, List.flatMap_map]

end Sha256Bridge
