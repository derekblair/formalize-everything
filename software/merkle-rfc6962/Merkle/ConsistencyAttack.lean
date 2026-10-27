import Merkle.InclusionAttack

/-! D1/D2 regressions: without fixed digest width, an injective hash permits
both a non-prefix consistency acceptance and two distinct trees with equal roots.
The concrete evaluations use kernel `decide`; the identity-hash facts are reused
from milestone 2a. No verifier or hash-tree definition changes. -/

namespace Merkle.ConsistencyAttack

open Merkle.VerifierCases (diagnosticHash)
open Merkle.InclusionAttack (leaves proof diagnosticHash_injective
  diagnosticHash_no_collision diagnosticHash_not_fixedWidth)

def oldLeaves : List ByteArray := [ByteArray.mk #[]]

theorem old_root_bytes : MTH diagnosticHash oldLeaves = ByteArray.mk #[0x00] := by
  decide +kernel

/-- The unchanged verifier accepts a one-leaf tree containing the empty byte
string against the two-leaf tree `[#[0x78], #[0x79]]`. -/
theorem shifted_parse_accepts :
    verifyConsistency diagnosticHash oldLeaves.length leaves.length
      (MTH diagnosticHash oldLeaves) (MTH diagnosticHash leaves) proof = true := by
  decide +kernel

theorem shifted_parse_not_prefix : oldLeaves ≠ leaves.take oldLeaves.length := by
  decide +kernel

/-- Every size premise of consistency soundness holds, but its prefix conclusion
fails despite injectivity and absence of collisions; only fixed width is absent. -/
theorem shifted_parse_attack :
    0 < oldLeaves.length ∧ oldLeaves.length ≤ leaves.length ∧
    verifyConsistency diagnosticHash oldLeaves.length leaves.length
      (MTH diagnosticHash oldLeaves) (MTH diagnosticHash leaves) proof = true ∧
    oldLeaves ≠ leaves.take oldLeaves.length ∧
    (∀ x y : ByteArray, diagnosticHash x = diagnosticHash y → x = y) ∧
    ¬ Collides diagnosticHash ∧
    (∀ ℓ : Nat, ¬ FixedWidth diagnosticHash ℓ) := by
  exact ⟨by decide, by decide, shifted_parse_accepts, shifted_parse_not_prefix,
    diagnosticHash_injective, diagnosticHash_no_collision, diagnosticHash_not_fixedWidth⟩

def bindingLeaves : List ByteArray :=
  [ByteArray.mk #[0x78], ByteArray.mk #[0x00, 0x79]]

def bindingLeaves' : List ByteArray :=
  [ByteArray.mk #[0x78, 0x00], ByteArray.mk #[0x79]]

theorem binding_root_bytes :
    MTH diagnosticHash bindingLeaves = ByteArray.mk #[0x01, 0x00, 0x78, 0x00, 0x00, 0x79] := by
  decide +kernel

theorem binding_roots_eq :
    MTH diagnosticHash bindingLeaves = MTH diagnosticHash bindingLeaves' := by
  decide +kernel

theorem binding_leaves_ne : bindingLeaves ≠ bindingLeaves' := by
  decide +kernel

/-- Distinct two-leaf trees share a root without a hash collision. The two node
inputs are the same bytes with different child boundaries. -/
theorem binding_attack :
    MTH diagnosticHash bindingLeaves = MTH diagnosticHash bindingLeaves' ∧
    bindingLeaves ≠ bindingLeaves' ∧
    (∀ x y : ByteArray, diagnosticHash x = diagnosticHash y → x = y) ∧
    ¬ Collides diagnosticHash ∧
    (∀ ℓ : Nat, ¬ FixedWidth diagnosticHash ℓ) := by
  exact ⟨binding_roots_eq, binding_leaves_ne, diagnosticHash_injective,
    diagnosticHash_no_collision, diagnosticHash_not_fixedWidth⟩

end Merkle.ConsistencyAttack
