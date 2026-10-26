import Std

namespace Merkle

/-- Hashes remain abstract: no digest-width or cryptographic assumption is used. -/
abbrev Hash := ByteArray → ByteArray

/-- RFC 6962 §2.1: the single byte 0x00 prefixes leaf data. -/
def leafHash (H : Hash) (d : ByteArray) : ByteArray :=
  H (ByteArray.mk #[0] ++ d)

/-- RFC 6962 §2.1: the single byte 0x01 prefixes two child hashes. -/
def nodeHash (H : Hash) (left right : ByteArray) : ByteArray :=
  H (ByteArray.mk #[1] ++ left ++ right)

/-- Largest power of two strictly below `n`, for `1 < n`. -/
def split (n : Nat) : Nat := 2 ^ (n - 1).log2

theorem split_pos {n : Nat} (_h : 1 < n) : 0 < split n := by
  exact Nat.pow_pos (by decide)

theorem split_lt {n : Nat} (h : 1 < n) : split n < n := by
  have := Nat.log2_self_le (n := n - 1) (by omega)
  unfold split
  omega

theorem split_le_double {n : Nat} (h : 1 < n) : n ≤ 2 * split n := by
  have := Nat.lt_log2_self (n := n - 1)
  simp only [Nat.pow_succ] at this
  unfold split
  omega

/-- The split is a power of two and satisfies the RFC's defining bounds. -/
theorem split_spec {n : Nat} (h : 1 < n) :
    (∃ e, split n = 2 ^ e) ∧ split n < n ∧ n ≤ 2 * split n :=
  ⟨⟨(n - 1).log2, rfl⟩, split_lt h, split_le_double h⟩

/-- No larger power of two remains strictly below `n`. -/
theorem split_largest {n e : Nat} (hn : 1 < n) (he : 2 ^ e < n) :
    2 ^ e ≤ split n := by
  apply Nat.pow_le_pow_right (by decide)
  exact (Nat.le_log2 (by omega : n - 1 ≠ 0)).mpr (by omega)

/-- Prefixes extending past the left subtree retain the same split. -/
theorem split_prefix {n m : Nat} (hn : 1 < n) (hm : split n < m)
    (hmn : m ≤ n) : split m = split n := by
  have hp := split_pos hn
  have hu := split_le_double hn
  have he : (m - 1).log2 = (n - 1).log2 := by
    apply (Nat.log2_eq_iff (by omega)).mpr
    constructor
    · change split n ≤ m - 1
      omega
    · rw [Nat.pow_succ]
      change m - 1 < split n * 2
      omega
  simp only [split, he]

/-- RFC 6962 §2.1, transcribed directly as list recursion. -/
def MTH (H : Hash) (ds : List ByteArray) : ByteArray :=
  if h0 : ds.length = 0 then H (ByteArray.mk #[])
  else if h1 : ds.length = 1 then leafHash H ds[0]
  else
    let k := split ds.length
    nodeHash H (MTH H (ds.take k)) (MTH H (ds.drop k))
termination_by ds.length
decreasing_by
  · simp only [List.length_take]
    have := split_lt (n := ds.length) (by omega)
    omega
  · simp only [List.length_drop]
    have := split_pos (n := ds.length) (by omega)
    omega

@[simp] theorem MTH_nil (H : Hash) : MTH H [] = H (ByteArray.mk #[]) := by
  rw [MTH]
  simp

@[simp] theorem MTH_singleton (H : Hash) (d : ByteArray) :
    MTH H [d] = leafHash H d := by
  rw [MTH]
  simp

theorem MTH_eq (H : Hash) (ds : List ByteArray) (h : 1 < ds.length) :
    MTH H ds = nodeHash H (MTH H (ds.take (split ds.length)))
      (MTH H (ds.drop (split ds.length))) := by
  rw [MTH]
  simp only [show ds.length ≠ 0 by omega, show ds.length ≠ 1 by omega,
    ↓reduceDIte]

/-- RFC 6962 §2.1.1: sibling hashes are appended in leaf-to-root order.
The RFC defines this for `m < ds.length`; empty/singleton lists totalize to `[]`. -/
def PATH (H : Hash) (m : Nat) (ds : List ByteArray) : List ByteArray :=
  if _h : ds.length ≤ 1 then []
  else
    let k := split ds.length
    if m < k then PATH H m (ds.take k) ++ [MTH H (ds.drop k)]
    else PATH H (m - k) (ds.drop k) ++ [MTH H (ds.take k)]
termination_by ds.length
decreasing_by
  · simp only [List.length_take]
    have := split_lt (n := ds.length) (by omega)
    omega
  · simp only [List.length_drop]
    have := split_pos (n := ds.length) (by omega)
    omega

theorem PATH_base (H : Hash) (m : Nat) (ds : List ByteArray) (h : ds.length ≤ 1) :
    PATH H m ds = [] := by
  rw [PATH]
  simp only [h, ↓reduceDIte]

theorem PATH_eq (H : Hash) (m : Nat) (ds : List ByteArray) (h : 1 < ds.length) :
    PATH H m ds = if m < split ds.length then
      PATH H m (ds.take (split ds.length)) ++ [MTH H (ds.drop (split ds.length))]
    else PATH H (m - split ds.length) (ds.drop (split ds.length)) ++
      [MTH H (ds.take (split ds.length))] := by
  rw [PATH]
  simp only [show ¬ds.length ≤ 1 by omega, ↓reduceDIte]

/-- RFC 6962 §2.1.2. `b = true` means the old root is already known.
The `m = length` case therefore omits its node exactly when `b = true`.
Outside the RFC's valid domain, non-equal lists of length ≤ 1 totalize to `[]`. -/
def SUBPROOF (H : Hash) (m : Nat) (ds : List ByteArray) (b : Bool) : List ByteArray :=
  if m = ds.length then
    if b then [] else [MTH H ds]
  else if _h : ds.length ≤ 1 then []
  else
    let k := split ds.length
    if m ≤ k then SUBPROOF H m (ds.take k) b ++ [MTH H (ds.drop k)]
    else SUBPROOF H (m - k) (ds.drop k) false ++ [MTH H (ds.take k)]
termination_by ds.length
decreasing_by
  · simp only [List.length_take]
    have := split_lt (n := ds.length) (by omega)
    omega
  · simp only [List.length_drop]
    have := split_pos (n := ds.length) (by omega)
    omega

theorem SUBPROOF_base (H : Hash) (ds : List ByteArray) (b : Bool) :
    SUBPROOF H ds.length ds b = if b then [] else [MTH H ds] := by
  rw [SUBPROOF]
  simp only [↓reduceIte]

theorem SUBPROOF_eq (H : Hash) (m : Nat) (ds : List ByteArray) (b : Bool)
    (hm : m < ds.length) (hn : 1 < ds.length) :
    SUBPROOF H m ds b = if m ≤ split ds.length then
      SUBPROOF H m (ds.take (split ds.length)) b ++ [MTH H (ds.drop (split ds.length))]
    else SUBPROOF H (m - split ds.length) (ds.drop (split ds.length)) false ++
      [MTH H (ds.take (split ds.length))] := by
  rw [SUBPROOF]
  simp only [show m ≠ ds.length by omega, show ¬ds.length ≤ 1 by omega,
    ↓reduceIte, ↓reduceDIte]

/-- RFC 6962 §2.1.2: PROOF is SUBPROOF with the old root known. -/
def consistencyProof (H : Hash) (m : Nat) (ds : List ByteArray) : List ByteArray :=
  SUBPROOF H m ds true

/-- MTH of RFC's half-open interval D[lo:hi]. -/
def subtreeMTH (H : Hash) (ds : List ByteArray) (lo hi : Nat) : ByteArray :=
  MTH H ((ds.drop lo).take (hi - lo))

@[simp] theorem subtreeMTH_zero (H : Hash) (ds : List ByteArray) (hi : Nat) :
    subtreeMTH H ds 0 hi = MTH H (ds.take hi) := by
  simp [subtreeMTH]

@[simp] theorem subtreeMTH_full (H : Hash) (ds : List ByteArray) :
    subtreeMTH H ds 0 ds.length = MTH H ds := by
  simp [subtreeMTH]

@[simp] theorem subtreeMTH_empty (H : Hash) (ds : List ByteArray) (lo : Nat) :
    subtreeMTH H ds lo lo = H (ByteArray.mk #[]) := by
  simp [subtreeMTH]

/-- A prefix extending into the right subtree splits at the original `k`. -/
theorem MTH_take_right (H : Hash) (ds : List ByteArray) (m : Nat)
    (hn : 1 < ds.length) (hm : split ds.length < m) (hmn : m ≤ ds.length) :
    MTH H (ds.take m) = nodeHash H (MTH H (ds.take (split ds.length)))
      (MTH H ((ds.drop (split ds.length)).take (m - split ds.length))) := by
  have hp := split_pos hn
  have hlen : (ds.take m).length = m := by simp [List.length_take, Nat.min_eq_left hmn]
  rw [MTH_eq H (ds.take m) (by omega), hlen, split_prefix hn hm hmn]
  rw [List.take_take, Nat.min_eq_left (by omega : split ds.length ≤ m), List.drop_take]

end Merkle
