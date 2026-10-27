import Sha256Bridge.Compression
import Sha256Bridge.Bytes
import Sha256Bridge.Fold
import Sha256Bridge.Domain
import Sha256Bridge.Vectors

/-!
Pure Lean equivalence between the pinned LeanSha256 implementation and the
independent bit-string specification. These theorems discharge none of
SizzLean's C/OpenSSL FFI equivalence axioms.
-/

namespace Sha256Bridge

open Hash.Sha256

/-- Transport all complete blocks, preserving their increasing order. -/
theorem blocks_eq_fast (P : ByteArray) (n : Nat) (hn : n * 64 ≤ P.size)
    (H : Fast.St) :
    Nat.fold n (fun i _ st => Upstream.compressBlock st (Upstream.extractBlock P i)) H.toArray =
      (Nat.fold n (fun i _ st => Fast.compress st (Fast.wordsAt P (64 * i))) H).toArray := by
  symm
  apply Fast.fold_abs Vector.toArray
  intro i hi st
  rw [extractBlock_eq_fast P i (by omega), compressBlock_eq_fast]

/-- Equivalence to the verified native-width implementation on every byte array. -/
theorem hash_eq_fast (data : ByteArray) : LeanSha256.hash data = Fast.sha256 data := by
  change Upstream.packState
    (Nat.fold ((Upstream.pad data).size / 64)
      (fun i _ st => Upstream.compressBlock st (Upstream.extractBlock (Upstream.pad data) i))
      Upstream.h0Constants) = _
  rw [h0Constants_eq_fast, blocks_eq_fast _ _ (by omega), packState_eq_fast, pad_eq_fast]
  rw [Fast.sha256, Fast.hashAll, hashFrom_eq_fold]
  simp only [Nat.zero_add]

/-- Every byte array agrees byte-for-byte with the independent specification. -/
theorem hash_toList_eq_spec_bytes (data : ByteArray) :
    (LeanSha256.hash data).data.toList = Spec.sha256_bytes data.data.toList := by
  rw [hash_eq_fast, Fast.sha256_eq_impl, Bridge.sha256_bridge]

/-- Total bit-level equality; beyond the FIPS domain both lengths wrap modulo `2^64`. -/
theorem hash_bits_eq_spec_unconditional (data : ByteArray) :
    Spec.bitsOfBytes (LeanSha256.hash data).data.toList =
      Spec.sha256 (Spec.bitsOfBytes data.data.toList) := by
  rw [hash_toList_eq_spec_bytes, Spec.sha256_bytes, Spec.bitsOfBytes_bytesOfBits]
  rw [Spec.length_sha256]

/-- The bit-level bridge restricted to the FIPS message domain. The companion
`spec_pad_length_no_wraparound` certifies that the length suffix is exact here. -/
theorem hash_bits_eq_fips_spec (data : ByteArray) (_h : data.size < 2 ^ 61) :
    Spec.bitsOfBytes (LeanSha256.hash data).data.toList =
      Spec.sha256 (Spec.bitsOfBytes data.data.toList) :=
  hash_bits_eq_spec_unconditional data

/-- Direct equality with lean4-hash's public digest API. -/
theorem hash_eq_lean4_hash (data : ByteArray) :
    LeanSha256.hash data = (Hash.Sha256.sha256 data).bytes := hash_eq_fast data

/-- Canonical reconstruction from the specification's bytes. -/
theorem hash_eq_of_spec_bytes (data : ByteArray) :
    LeanSha256.hash data = (Spec.sha256_bytes data.data.toList).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.toList_data_toByteArray, hash_toList_eq_spec_bytes]

/-- The bounded bit-level bridge for concatenating two inputs. -/
theorem combine_bits_eq_fips_spec (left right : ByteArray)
    (h : left.size + right.size < 2 ^ 61) :
    Spec.bitsOfBytes (LeanSha256.combine left right).data.toList =
      Spec.sha256 (Spec.bitsOfBytes left.data.toList ++ Spec.bitsOfBytes right.data.toList) := by
  have hb : (left ++ right).size < 2 ^ 61 := by simpa using h
  simpa only [LeanSha256.combine, ByteArray.toList_data_append, Bridge.bitsOfBytes_append]
    using hash_bits_eq_fips_spec (left ++ right) hb

/-- Unconditional byte-level equality for the pure combine operation. -/
theorem combine_toList_eq_spec_bytes (left right : ByteArray) :
    (LeanSha256.combine left right).data.toList =
      Spec.sha256_bytes (left.data.toList ++ right.data.toList) := by
  simpa only [LeanSha256.combine, ByteArray.toList_data_append]
    using hash_toList_eq_spec_bytes (left ++ right)

/-- The exact pure zip/map batch expression, including zip's truncation behavior. -/
theorem batch_combine_map_eq_spec_bytes (lefts rights : Array ByteArray) :
    ((lefts.zip rights).map fun (l, r) => (LeanSha256.combine l r).data.toList) =
      (lefts.zip rights).map fun (l, r) =>
        Spec.sha256_bytes (l.data.toList ++ r.data.toList) := by
  simp only [combine_toList_eq_spec_bytes]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The SHA-256 digest prefix differs from the SHA-224 empty digest.
The SHA-256 value is reused from the empty kernel gate; only the one-block
SHA-224 calculation is reduced here. -/
theorem hash_empty_take28_ne_sha224_empty :
    ((LeanSha256.hash ByteArray.empty).data.toList).take 28 ≠ Hash.Sha256.Impl.sha224 [] := by
  rw [Vectors.empty]
  decide +kernel

end Sha256Bridge
