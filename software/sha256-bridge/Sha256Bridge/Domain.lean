import Hash.Sha256

/-! The FIPS message bound makes the specification's length field exact. -/

namespace Sha256Bridge

/-- Below `2^61` bytes, the 64-bit suffix encodes the full bit length. -/
theorem spec_pad_length_no_wraparound (data : ByteArray) (h : data.size < 2 ^ 61) :
    Hash.Sha256.Spec.natOfBits
      (Hash.Sha256.Spec.bitsOfNat 64
        (Hash.Sha256.Spec.bitsOfBytes data.data.toList).length) = 8 * data.size := by
  rw [Hash.Sha256.Spec.natOfBits_bitsOfNat, Hash.Sha256.Spec.length_bitsOfBytes,
    Array.length_toList]
  change (8 * data.size) % 2 ^ 64 = 8 * data.size
  apply Nat.mod_eq_of_lt
  omega

end Sha256Bridge
