import Merkle.Audit
import Merkle.Consistency

/-! Small executable verifier regressions checked by the kernel. The identity
hash exposes byte ordering for diagnosis; it is not cryptography. These concrete
rejections do not assert general collision resistance or milestone-2 soundness. -/

namespace Merkle.VerifierCases

def diagnosticHash : Hash := fun bytes => bytes

def leaves : List ByteArray :=
  [ByteArray.mk #[10], ByteArray.mk #[11], ByteArray.mk #[12],
   ByteArray.mk #[13], ByteArray.mk #[14], ByteArray.mk #[15], ByteArray.mk #[16]]

def root7 : ByteArray := MTH diagnosticHash leaves
def root3 : ByteArray := MTH diagnosticHash (leaves.take 3)
def proof3 : List ByteArray := consistencyProof diagnosticHash 3 leaves

theorem audit_honest_seven :
    verifyAudit diagnosticHash 6 7 (ByteArray.mk #[16])
      (PATH diagnosticHash 6 leaves) root7 = true := by
  decide +kernel

theorem audit_empty :
    verifyAudit diagnosticHash 0 0 (ByteArray.mk #[10]) []
      (MTH diagnosticHash []) = false := by
  decide +kernel

theorem audit_out_of_range :
    verifyAudit diagnosticHash 7 7 (ByteArray.mk #[16])
      (PATH diagnosticHash 6 leaves) root7 = false := by
  decide +kernel

theorem audit_missing_sibling :
    verifyAudit diagnosticHash 6 7 (ByteArray.mk #[16])
      ((PATH diagnosticHash 6 leaves).drop 1) root7 = false := by
  decide +kernel

theorem audit_extra_sibling :
    verifyAudit diagnosticHash 6 7 (ByteArray.mk #[16])
      (PATH diagnosticHash 6 leaves ++ [ByteArray.mk #[99]]) root7 = false := by
  decide +kernel

theorem audit_wrong_root :
    verifyAudit diagnosticHash 6 7 (ByteArray.mk #[16])
      (PATH diagnosticHash 6 leaves) (ByteArray.mk #[99]) = false := by
  decide +kernel

/-- Presenting the left leaf and its sibling at the right index reverses the
node inputs, which this concrete diagnostic hash distinguishes. -/
theorem audit_swapped_orientation :
    verifyAudit diagnosticHash 1 2 (ByteArray.mk #[10])
      [leafHash diagnosticHash (ByteArray.mk #[11])]
      (MTH diagnosticHash (leaves.take 2)) = false := by
  decide +kernel

theorem consistency_zero :
    verifyConsistency diagnosticHash 0 7 (MTH diagnosticHash []) root7 [] = false := by
  decide +kernel

theorem consistency_oversized :
    verifyConsistency diagnosticHash 8 7 root7 root7 [] = false := by
  decide +kernel

theorem consistency_equal_empty :
    verifyConsistency diagnosticHash 7 7 root7 root7 [] = true := by
  decide +kernel

theorem consistency_equal_extra :
    verifyConsistency diagnosticHash 7 7 root7 root7 [root7] = false := by
  decide +kernel

theorem consistency_missing_node :
    verifyConsistency diagnosticHash 3 7 root3 root7 (proof3.drop 1) = false := by
  decide +kernel

theorem consistency_extra_node :
    verifyConsistency diagnosticHash 3 7 root3 root7
      (proof3 ++ [ByteArray.mk #[99]]) = false := by
  decide +kernel

theorem consistency_wrong_old_root :
    verifyConsistency diagnosticHash 3 7 (ByteArray.mk #[99]) root7 proof3 = false := by
  decide +kernel

theorem consistency_wrong_new_root :
    verifyConsistency diagnosticHash 3 7 root3 (ByteArray.mk #[99]) proof3 = false := by
  decide +kernel

/-- The complete left subtree is supplied by the known old root, so only the
right subtree appears in the proof: no redundant seed node is accepted. -/
theorem consistency_four_seed_omitted :
    verifyConsistency diagnosticHash 4 7 (MTH diagnosticHash (leaves.take 4)) root7
      [MTH diagnosticHash (leaves.drop 4)] = true := by
  decide +kernel

end Merkle.VerifierCases
