import Merkle.VerifierCases
import Merkle.ByteAlgebra

/-! D1's shifted-parse inclusion attack under an injective, variable-width hash.
These are kernel-checked counterexamples to removing `FixedWidth` from inclusion
soundness. They exercise the unchanged milestone-1 verifier. -/

namespace Merkle.InclusionAttack

open Merkle.VerifierCases (diagnosticHash)

def leaves : List ByteArray := [ByteArray.mk #[0x78], ByteArray.mk #[0x79]]

def proof : List ByteArray := [ByteArray.mk #[0x78, 0x00, 0x79]]

theorem honest_root_bytes :
    MTH diagnosticHash leaves = ByteArray.mk #[0x01, 0x00, 0x78, 0x00, 0x79] := by
  decide +kernel

/-- The empty forged leaf consumes the whole supplied proof and reaches the
honest two-leaf root, shifting the child boundary one byte to the left. -/
theorem shifted_parse_accepts :
    verifyAudit diagnosticHash 0 leaves.length (ByteArray.mk #[]) proof
      (MTH diagnosticHash leaves) = true := by
  decide +kernel

theorem shifted_parse_leaf_ne : ByteArray.mk #[] ≠ leaves[0] := by
  decide +kernel

theorem diagnosticHash_injective :
    ∀ x y : ByteArray, diagnosticHash x = diagnosticHash y → x = y := by
  intro x y h
  exact h

theorem diagnosticHash_no_collision : ¬ Collides diagnosticHash := by
  rintro ⟨x, y, hne, heq⟩
  exact hne (diagnosticHash_injective x y heq)

theorem diagnosticHash_not_fixedWidth (ℓ : Nat) : ¬ FixedWidth diagnosticHash ℓ := by
  intro hw
  have h0 := hw (ByteArray.mk #[])
  have h1 := hw (ByteArray.mk #[0])
  change 0 = ℓ at h0
  change 1 = ℓ at h1
  omega

/-- Acceptance with a different leaf despite an injective hash: a collision
cannot explain this attack, and no fixed output width holds. -/
theorem shifted_parse_attack :
    verifyAudit diagnosticHash 0 leaves.length (ByteArray.mk #[]) proof
      (MTH diagnosticHash leaves) = true ∧
    ByteArray.mk #[] ≠ leaves[0] ∧
    (∀ x y : ByteArray, diagnosticHash x = diagnosticHash y → x = y) ∧
    ¬ Collides diagnosticHash ∧
    (∀ ℓ : Nat, ¬ FixedWidth diagnosticHash ℓ) := by
  exact ⟨shifted_parse_accepts, shifted_parse_leaf_ne, diagnosticHash_injective,
    diagnosticHash_no_collision, diagnosticHash_not_fixedWidth⟩

end Merkle.InclusionAttack
