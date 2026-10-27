import Merkle.Vectors
import Merkle.VerifierCases
import Merkle.ByteAlgebra
import Merkle.AuditStructure
import Merkle.Soundness
import Merkle.InclusionAttack
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Build-enforced, transitive axiom audit. Select declarations by their originating
project module, not just their public namespace: private helpers and generated
equations/termination declarations are included. No local axiom declarations
are allowed, and dependencies may use only the standard three axioms below.
Set MERKLE_AUDIT_VERBOSE=1 when elaborating this file to print every result.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let verbose := (← IO.getEnv "MERKLE_AUDIT_VERBOSE") == some "1"
  let mut count : Nat := 0
  let mut used : Array Name := #[]
  let declarations := env.constants.toList.toArray.qsort (fun a b => Name.lt a.1 b.1)
  for (name, info) in declarations do
    let projectModule := match env.getModuleIdxFor? name with
      | some idx => (`Merkle).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => (`Merkle).isPrefixOf name
    if projectModule then
      if let .axiomInfo _ := info then
        throwError "Project declares an axiom: {name}"
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
        unless used.contains axiomName do
          used := used.push axiomName
      if verbose then
        logInfo m!"AUDIT {name}: {axioms}"
      count := count + 1
  logInfo m!"Axiom audit passed for {count} project declarations (including private/generated); used: {used.qsort Name.lt}."

#print axioms Merkle.split
#print axioms Merkle.split_largest
#print axioms Merkle.leafHash
#print axioms Merkle.nodeHash
#print axioms Merkle.MTH
#print axioms Merkle.PATH
#print axioms Merkle.SUBPROOF
#print axioms Merkle.subtreeMTH
#print axioms Merkle.auditWalk
#print axioms Merkle.verifyAudit
#print axioms Merkle.consistencyRoots
#print axioms Merkle.verifyConsistency
#print axioms Merkle.auditWalk_complete
#print axioms Merkle.consistencyRoots_complete
#print axioms Merkle.audit_complete
#print axioms Merkle.consistency_complete

-- M2a: hypotheses, every new theorem, and the shifted-parse regression.
#print axioms Merkle.Collides
#print axioms Merkle.FixedWidth
#print axioms Merkle.empty_ne_leaf
#print axioms Merkle.empty_ne_node
#print axioms Merkle.leaf_ne_node
#print axioms Merkle.leaf_inj
#print axioms Merkle.node_inj_left
#print axioms Merkle.node_inj_right
#print axioms Merkle.leafHash_eq
#print axioms Merkle.nodeHash_eq_left
#print axioms Merkle.nodeHash_eq_right
#print axioms Merkle.leafHash_size
#print axioms Merkle.nodeHash_size
#print axioms Merkle.MTH_size
#print axioms Merkle.auditWalk_left_inv
#print axioms Merkle.auditWalk_right_inv
#print axioms Merkle.auditWalk_one_inv
#print axioms Merkle.auditWalk_size
#print axioms Merkle.auditWalk_extract
#print axioms Merkle.audit_sound
#print axioms Merkle.audit_sound_of_injective
#print axioms Merkle.InclusionAttack.honest_root_bytes
#print axioms Merkle.InclusionAttack.shifted_parse_accepts
#print axioms Merkle.InclusionAttack.shifted_parse_leaf_ne
#print axioms Merkle.InclusionAttack.diagnosticHash_injective
#print axioms Merkle.InclusionAttack.diagnosticHash_no_collision
#print axioms Merkle.InclusionAttack.diagnosticHash_not_fixedWidth
#print axioms Merkle.InclusionAttack.shifted_parse_attack
