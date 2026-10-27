import Utf8.Examples
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Build-enforced, transitive axiom audit, in the style of the sibling
targets (Merkle's `Checks.lean`, Bech32's `Audit.lean`). Declarations
are selected by their originating project module, not just their
public namespace: private helpers and generated equations/termination
declarations are included. No local axiom declarations are allowed,
and dependencies may use only the standard three axioms below.
Set `UTF8_AUDIT_VERBOSE=1` when elaborating this file to print every
declaration's result.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let verbose := (← IO.getEnv "UTF8_AUDIT_VERBOSE") == some "1"
  let mut count : Nat := 0
  let mut used : Array Name := #[]
  let declarations := env.constants.toList.toArray.qsort
    (fun a b => Name.lt a.1 b.1)
  for (name, info) in declarations do
    let projectModule := match env.getModuleIdxFor? name with
      | some idx => (`Utf8).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => (`Utf8).isPrefixOf name
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

#print axioms Utf8.Seq
#print axioms Utf8.Valid
#print axioms Utf8.encodeCodepoint
#print axioms Utf8.encodeAll
#print axioms Utf8.decodeSeq?
#print axioms Utf8.decode
#print axioms Utf8.encode_payload2
#print axioms Utf8.encode_payload3
#print axioms Utf8.encode_payload4
#print axioms Utf8.seq_encodeCodepoint
#print axioms Utf8.valid_encodeAll
#print axioms Utf8.decodeSeq?_of_seq
#print axioms Utf8.decodeSeq?_encodeCodepoint
#print axioms Utf8.valid_iff_decode
#print axioms Utf8.decode_encodeAll
#print axioms Utf8.decode_eq_none_iff
#print axioms Utf8.encodeCodepoint_eq_core
#print axioms Utf8.valid_iff_core
#print axioms Utf8.valid_iff_validate
#print axioms Utf8.valid_iff_exists_string
#print axioms Utf8.Examples.valid_gothic
#print axioms Utf8.Examples.valid_max
#print axioms Utf8.Examples.invalid_surrogate_low
#print axioms Utf8.Examples.invalid_above_max
#print axioms Utf8.Examples.not_valid_overlong_two
#print axioms Utf8.Examples.not_valid_surrogate
#print axioms Utf8.Examples.not_valid_overlong_e0
#print axioms Utf8.Examples.not_valid_overlong_f0
#print axioms Utf8.Examples.not_valid_above_max
