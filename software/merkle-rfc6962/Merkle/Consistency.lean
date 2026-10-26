import Merkle.Spec

namespace Merkle

/-- Reconstruct both roots from the RFC §2.1.2 subproof, leaving unused nodes.
`known` supplies the old root only in the `b = true` base case. The traversal
uses sizes alone; it has no access to the original leaves or generators. -/
def consistencyRoots (H : Hash) (m n : Nat) (b : Bool) (known : ByteArray)
    (proof : List ByteArray) : Option (ByteArray × ByteArray × List ByteArray) :=
  if m = n then
    if b then some (known, known, proof)
    else match proof with
      | [] => none
      | seed :: rest => some (seed, seed, rest)
  else if _hn : 1 < n then
    let k := split n
    if m ≤ k then
      match consistencyRoots H m k b known proof with
      | some (old, current, sibling :: tail) =>
        some (old, nodeHash H current sibling, tail)
      | _ => none
    else
      match consistencyRoots H (m - k) (n - k) false known proof with
      | some (old, current, sibling :: tail) =>
        some (nodeHash H sibling old, nodeHash H sibling current, tail)
      | _ => none
  else none
termination_by n
decreasing_by
  · exact split_lt _hn
  · have := split_pos _hn
    omega

/-- Verify a consistency proof by recomputing and comparing both roots.
The sizes must satisfy `0 < m ≤ n`, and every supplied proof node must be used.
Equal nonzero sizes require an empty proof and equal roots. -/
def verifyConsistency (H : Hash) (m n : Nat) (oldRoot newRoot : ByteArray)
    (proof : List ByteArray) : Bool :=
  if 0 < m ∧ m ≤ n then
    match consistencyRoots H m n true oldRoot proof with
    | some (old, current, []) => decide (old = oldRoot ∧ current = newRoot)
    | _ => false
  else false

/-- Honest subproofs reconstruct the two subtree roots and consume precisely
their own nodes. If the seed is omitted, the supplied known root must be right. -/
theorem consistencyRoots_complete (H : Hash) (ds : List ByteArray) (m : Nat)
    (b : Bool) (known : ByteArray) (tail : List ByteArray)
    (hm : 0 < m) (hmn : m ≤ ds.length)
    (hknown : b = true → known = MTH H (ds.take m)) :
    consistencyRoots H m ds.length b known (SUBPROOF H m ds b ++ tail) =
      some (MTH H (ds.take m), MTH H ds, tail) := by
  by_cases heq : m = ds.length
  · subst m
    rw [SUBPROOF_base, consistencyRoots.eq_def]
    simp only [↓reduceIte, List.take_length]
    cases b with
    | false => rfl
    | true => simpa using hknown rfl
  · have hn : 1 < ds.length := by omega
    have hkpos := split_pos hn
    have hklt := split_lt hn
    have hleft : (ds.take (split ds.length)).length = split ds.length := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hklt)]
    have hright : (ds.drop (split ds.length)).length = ds.length - split ds.length :=
      List.length_drop
    rw [SUBPROOF_eq H m ds b (by omega) hn, consistencyRoots.eq_def]
    simp only [heq, ↓reduceIte, hn, ↓reduceDIte]
    by_cases hmk : m ≤ split ds.length
    · simp only [hmk, ↓reduceIte, List.append_assoc, List.singleton_append]
      have ht : (ds.take (split ds.length)).take m = ds.take m := by
        rw [List.take_take, Nat.min_eq_left hmk]
      have ih := consistencyRoots_complete H (ds.take (split ds.length)) m b known
        (MTH H (ds.drop (split ds.length)) :: tail) hm (by omega)
        (by simpa only [ht] using hknown)
      rw [hleft] at ih
      rw [ih]
      simp only [ht]
      rw [MTH_eq H ds hn]
    · simp only [hmk, ↓reduceIte, List.append_assoc, List.singleton_append]
      have ih := consistencyRoots_complete H (ds.drop (split ds.length))
        (m - split ds.length) false known
        (MTH H (ds.take (split ds.length)) :: tail) (by omega)
        (by simp only [List.length_drop]; omega) (by simp)
      rw [hright] at ih
      rw [ih]
      rw [MTH_take_right H ds m hn (by omega) hmn, MTH_eq H ds hn]
termination_by ds.length
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

/-- Every honestly generated consistency proof verifies, for arbitrary hashes
and leaves, including equal nonempty tree sizes. -/
theorem consistency_complete (H : Hash) (ds : List ByteArray) (m : Nat)
    (hm : 0 < m) (hmn : m ≤ ds.length) :
    verifyConsistency H m ds.length (MTH H (ds.take m)) (MTH H ds)
      (consistencyProof H m ds) = true := by
  unfold verifyConsistency consistencyProof
  simp only [hm, hmn, and_self, ↓reduceIte]
  have h := consistencyRoots_complete H ds m true (MTH H (ds.take m)) [] hm hmn
    (by intros; rfl)
  simp only [List.append_nil] at h
  rw [h]
  simp

end Merkle
