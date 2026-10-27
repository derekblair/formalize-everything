import Merkle.Audit
import Merkle.ByteAlgebra

namespace Merkle

/-- A successful left branch consumes one sibling after its recursive walk. -/
theorem auditWalk_left_inv (H : Hash) (m n : Nat) (leaf : ByteArray)
    (proof : List ByteArray) (r : ByteArray) (rest : List ByteArray)
    (hn : 1 < n) (hm : m < split n)
    (hwalk : auditWalk H m n leaf proof = some (r, rest)) :
    ∃ child sibling,
      auditWalk H m (split n) leaf proof = some (child, sibling :: rest) ∧
      r = nodeHash H child sibling := by
  rw [auditWalk, dite_eq_left hn, ite_eq_left hm] at hwalk
  cases hsub : auditWalk H m (split n) leaf proof with
  | none => simp [hsub] at hwalk
  | some result =>
    rcases result with ⟨child, tail⟩
    cases tail with
    | nil => simp [hsub] at hwalk
    | cons sibling tail =>
      simp only [hsub, Option.some.injEq, Prod.mk.injEq] at hwalk
      rcases hwalk with ⟨hr, hrest⟩
      subst tail
      exact ⟨child, sibling, rfl, hr.symm⟩

/-- A successful right branch consumes one sibling after its recursive walk. -/
theorem auditWalk_right_inv (H : Hash) (m n : Nat) (leaf : ByteArray)
    (proof : List ByteArray) (r : ByteArray) (rest : List ByteArray)
    (hn : 1 < n) (hm : ¬m < split n)
    (hwalk : auditWalk H m n leaf proof = some (r, rest)) :
    ∃ child sibling,
      auditWalk H (m - split n) (n - split n) leaf proof =
        some (child, sibling :: rest) ∧
      r = nodeHash H sibling child := by
  rw [auditWalk, dite_eq_left hn, ite_eq_right hm] at hwalk
  cases hsub : auditWalk H (m - split n) (n - split n) leaf proof with
  | none => simp [hsub] at hwalk
  | some result =>
    rcases result with ⟨child, tail⟩
    cases tail with
    | nil => simp [hsub] at hwalk
    | cons sibling tail =>
      simp only [hsub, Option.some.injEq, Prod.mk.injEq] at hwalk
      rcases hwalk with ⟨hr, hrest⟩
      subst tail
      exact ⟨child, sibling, rfl, hr.symm⟩

/-- At size one the walk hashes the leaf and leaves the proof untouched. -/
theorem auditWalk_one_inv (H : Hash) (m : Nat) (leaf : ByteArray)
    (proof : List ByteArray) (r : ByteArray) (rest : List ByteArray)
    (hwalk : auditWalk H m 1 leaf proof = some (r, rest)) :
    r = leafHash H leaf ∧ rest = proof := by
  rw [auditWalk] at hwalk
  simpa only [Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte, Option.some.injEq,
    Prod.mk.injEq, eq_comm] using hwalk

/-- Every returned root is an `H`-output, regardless of supplied sibling widths.
This is a branch analysis, not an induction on the walk. -/
theorem auditWalk_size (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (m n : Nat) (leaf : ByteArray) (proof : List ByteArray)
    (r : ByteArray) (rest : List ByteArray)
    (hwalk : auditWalk H m n leaf proof = some (r, rest)) : r.size = ℓ := by
  by_cases hn : 1 < n
  · by_cases hm : m < split n
    · obtain ⟨child, sibling, _, hr⟩ :=
        auditWalk_left_inv H m n leaf proof r rest hn hm hwalk
      rw [hr]
      exact nodeHash_size H ℓ hw child sibling
    · obtain ⟨child, sibling, _, hr⟩ :=
        auditWalk_right_inv H m n leaf proof r rest hn hm hwalk
      rw [hr]
      exact nodeHash_size H ℓ hw sibling child
  · by_cases hone : n = 1
    · subst n
      rw [(auditWalk_one_inv H m leaf proof r rest hwalk).1]
      exact leafHash_size H ℓ hw leaf
    · rw [auditWalk, dite_eq_right hn, ite_eq_right hone] at hwalk
      contradiction

end Merkle
