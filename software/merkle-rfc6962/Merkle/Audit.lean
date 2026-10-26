import Merkle.Spec

namespace Merkle

/-- Recompute the root along the size-determined branch, consuming sibling hashes
in leaf-to-root order. The unused suffix is returned so callers can reject extra
nodes. Only the leaf, its index, the tree size, and the proof are available here;
the verifier never receives the other leaf inputs. -/
def auditWalk (H : Hash) (m n : Nat) (leaf : ByteArray)
    (proof : List ByteArray) : Option (ByteArray × List ByteArray) :=
  if _h : 1 < n then
    let k := split n
    if m < k then
      match auditWalk H m k leaf proof with
      | some (root, sibling :: rest) => some (nodeHash H root sibling, rest)
      | _ => none
    else
      match auditWalk H (m - k) (n - k) leaf proof with
      | some (root, sibling :: rest) => some (nodeHash H sibling root, rest)
      | _ => none
  else if n = 1 then some (leafHash H leaf, proof)
  else none
termination_by n
decreasing_by
  · exact split_lt _h
  · have := split_pos _h
    omega

/-- RFC 6962 §2.1.1's root-recomputation comparison. Reject out-of-range
indices, missing/extra siblings, and a recomputed root unequal to `root`. -/
def verifyAudit (H : Hash) (m n : Nat) (leaf : ByteArray)
    (proof : List ByteArray) (root : ByteArray) : Bool :=
  if m < n then
    match auditWalk H m n leaf proof with
    | some (actual, []) => decide (actual = root)
    | _ => false
  else false

/-- The honest path consumes exactly its own nodes, even before a suffix. -/
theorem auditWalk_complete (H : Hash) (ds : List ByteArray) (m : Nat)
    (hm : m < ds.length) (tail : List ByteArray) :
    auditWalk H m ds.length ds[m] (PATH H m ds ++ tail) =
      some (MTH H ds, tail) := by
  by_cases hn : 1 < ds.length
  · have hk := split_lt hn
    have hp := split_pos hn
    have hlen : (ds.take (split ds.length)).length = split ds.length := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    rw [auditWalk, dite_eq_left hn, PATH_eq H m ds hn, MTH_eq H ds hn]
    by_cases hmleft : m < split ds.length
    · simp only [hmleft, ↓reduceIte, List.append_assoc, List.singleton_append]
      have hml : m < (ds.take (split ds.length)).length := by omega
      have hr :=  auditWalk_complete H (ds.take (split ds.length)) m hml
        (MTH H (ds.drop (split ds.length)) :: tail)
      simp only [hlen, List.getElem_take] at hr
      rw [hr]
    · simp only [hmleft, ↓reduceIte, List.append_assoc, List.singleton_append]
      have hmr : m - split ds.length < (ds.drop (split ds.length)).length := by
        simp only [List.length_drop]
        omega
      have hr :=  auditWalk_complete H (ds.drop (split ds.length))
        (m - split ds.length) hmr (MTH H (ds.take (split ds.length)) :: tail)
      have hidx : split ds.length + (m - split ds.length) = m := by omega
      simp only [List.length_drop, List.getElem_drop, hidx] at hr
      rw [hr]
  · cases ds with
    | nil => simp at hm
    | cons d rest =>
      cases rest with
      | nil =>
        have hzero : m = 0 := by simp at hm; omega
        subst m
        simp [auditWalk, PATH_base, MTH_singleton]
      | cons d' rest => simp at hn
termination_by ds.length
decreasing_by
  · simp only [List.length_take]
    have := split_lt hn
    omega
  · simp only [List.length_drop]
    have := split_pos hn
    omega

/-- Every honestly generated audit path verifies for every valid leaf index,
for an arbitrary hash function and arbitrary list of leaf inputs. -/
theorem audit_complete (H : Hash) (ds : List ByteArray) (m : Nat)
    (hm : m < ds.length) :
    verifyAudit H m ds.length ds[m] (PATH H m ds) (MTH H ds) = true := by
  have hw := auditWalk_complete H ds m hm []
  simp only [List.append_nil] at hw
  simp [verifyAudit, hm, hw]

end Merkle
