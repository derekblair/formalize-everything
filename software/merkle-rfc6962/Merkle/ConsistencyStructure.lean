import Merkle.Consistency
import Merkle.ByteAlgebra

namespace Merkle

/-- A successful left branch preserves the old root and consumes one sibling
after the recursive walk. -/
theorem consistencyRoots_left_inv (H : Hash) (m n : Nat) (b : Bool)
    (known : ByteArray) (proof : List ByteArray) (old current : ByteArray)
    (rest : List ByteArray) (hne : m ≠ n) (hn : 1 < n) (hm : m ≤ split n)
    (hwalk : consistencyRoots H m n b known proof = some (old, current, rest)) :
    ∃ child sibling,
      consistencyRoots H m (split n) b known proof =
        some (old, child, sibling :: rest) ∧
      current = nodeHash H child sibling := by
  rw [consistencyRoots.eq_def, ite_eq_right hne, dite_eq_left hn, ite_eq_left hm] at hwalk
  cases hsub : consistencyRoots H m (split n) b known proof with
  | none => simp [hsub] at hwalk
  | some result =>
    rcases result with ⟨oldChild, currentChild, tail⟩
    cases tail with
    | nil => simp [hsub] at hwalk
    | cons sibling tail =>
      simp only [hsub, Option.some.injEq, Prod.mk.injEq] at hwalk
      rcases hwalk with ⟨hold, hcurrent, hrest⟩
      subst oldChild
      subst tail
      exact ⟨currentChild, sibling, rfl, hcurrent.symm⟩

/-- A successful right branch extends both roots with the same left sibling.
The recursive seed may still be an arbitrary byte string. -/
theorem consistencyRoots_right_inv (H : Hash) (m n : Nat) (b : Bool)
    (known : ByteArray) (proof : List ByteArray) (old current : ByteArray)
    (rest : List ByteArray) (hne : m ≠ n) (hn : 1 < n) (hm : ¬m ≤ split n)
    (hwalk : consistencyRoots H m n b known proof = some (old, current, rest)) :
    ∃ oldChild currentChild sibling,
      consistencyRoots H (m - split n) (n - split n) false known proof =
        some (oldChild, currentChild, sibling :: rest) ∧
      old = nodeHash H sibling oldChild ∧ current = nodeHash H sibling currentChild := by
  rw [consistencyRoots.eq_def, ite_eq_right hne, dite_eq_left hn, ite_eq_right hm] at hwalk
  cases hsub : consistencyRoots H (m - split n) (n - split n) false known proof with
  | none => simp [hsub] at hwalk
  | some result =>
    rcases result with ⟨oldChild, currentChild, tail⟩
    cases tail with
    | nil => simp [hsub] at hwalk
    | cons sibling tail =>
      simp only [hsub, Option.some.injEq, Prod.mk.injEq] at hwalk
      rcases hwalk with ⟨hold, hcurrent, hrest⟩
      subst tail
      exact ⟨oldChild, currentChild, sibling, rfl, hold.symm, hcurrent.symm⟩

/-- Equal sizes return equal components, for either flag. No width assertion is
possible here: the false branch returns its adversary-supplied seed unhashed. -/
theorem consistencyRoots_equal (H : Hash) (m n : Nat) (b : Bool)
    (known : ByteArray) (proof : List ByteArray) (old current : ByteArray)
    (rest : List ByteArray) (heq : m = n)
    (hwalk : consistencyRoots H m n b known proof = some (old, current, rest)) :
    old = current := by
  rw [consistencyRoots.eq_def, ite_eq_left heq] at hwalk
  cases b with
  | false =>
    cases proof with
    | nil => simp at hwalk
    | cons seed tail =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at hwalk
      exact hwalk.1.symm.trans hwalk.2.1
  | true =>
    simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hwalk
    exact hwalk.1.symm.trans hwalk.2.1

/-- A strict-size successful walk hashes its current root at the outer step.
This conditional width fact does not constrain the old root or an equal-size seed. -/
theorem consistencyRoots_current_size (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (m n : Nat) (b : Bool) (known : ByteArray) (proof : List ByteArray)
    (old current : ByteArray) (rest : List ByteArray) (hlt : m < n)
    (hwalk : consistencyRoots H m n b known proof = some (old, current, rest)) :
    current.size = ℓ := by
  have hne : m ≠ n := by omega
  by_cases hn : 1 < n
  · by_cases hm : m ≤ split n
    · obtain ⟨child, sibling, _, hcurrent⟩ :=
        consistencyRoots_left_inv H m n b known proof old current rest hne hn hm hwalk
      rw [hcurrent]
      exact nodeHash_size H ℓ hw child sibling
    · obtain ⟨oldChild, currentChild, sibling, _, _, hcurrent⟩ :=
        consistencyRoots_right_inv H m n b known proof old current rest hne hn hm hwalk
      rw [hcurrent]
      exact nodeHash_size H ℓ hw sibling currentChild
  · rw [consistencyRoots.eq_def, ite_eq_right hne, dite_eq_right hn] at hwalk
    contradiction

end Merkle
