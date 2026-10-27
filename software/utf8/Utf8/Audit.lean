import Utf8
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Build-enforced, transitive axiom audit over the complete library
import graph, in the style of the sibling targets (Merkle's
`Checks.lean`, Bech32's `Audit.lean`).

This entrypoint imports the umbrella module `Utf8`, so the
environment it audits is the library's whole import graph, not one
module's import chain. Declarations are selected by their
originating project module, not just their public namespace:
private helpers and generated equations/termination declarations
are included. No local axiom declarations are allowed, and
dependencies may use only the standard three axioms below.

Module-coverage guard: the set of project modules actually present
in the environment is derived from `env.header.moduleNames` and
compared against the explicit expected inventory
(`expectedModules`) in both directions. A project module present
in the import graph but missing from the inventory fails the
build, and so does an expected module absent from the import
graph — a module can no longer escape the audit by being imported
only from the umbrella. Two inventory entries are import-only and
declare nothing: the umbrella `Utf8` itself, and this audit
entrypoint `Utf8.Audit` (a module cannot appear in its own import
environment, so the entrypoint is accounted for by name rather
than by presence).

Set `UTF8_AUDIT_VERBOSE=1` when elaborating this file to print
every declaration's result.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let verbose := (← IO.getEnv "UTF8_AUDIT_VERBOSE") == some "1"
  -- Expected inventory of project modules. `Utf8` (the umbrella)
  -- and `Utf8.Audit` (this entrypoint) are import-only: they
  -- contribute no declarations of their own.
  let expectedModules : Array Name :=
    #[`Utf8, `Utf8.Spec, `Utf8.Decode, `Utf8.Char, `Utf8.Core,
      `Utf8.Examples, `Utf8.Audit]
  let entrypoint : Name := `Utf8.Audit
  -- Project modules actually present in this environment, derived
  -- from the environment header (the evidence), not from the
  -- inventory (the expectation).
  let presentModules : Array Name := env.header.moduleNames.filter
    (fun m => (`Utf8).isPrefixOf m)
  for m in presentModules do
    unless expectedModules.contains m do
      throwError "Axiom audit module-inventory mismatch: project module {m} is present in the library import graph but is not in the audit's expected module inventory"
  for m in expectedModules do
    unless m == entrypoint || presentModules.contains m do
      throwError "Axiom audit module-inventory mismatch: expected project module {m} is absent from the library import graph"
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
  logInfo m!"Axiom audit passed for {count} project declarations (including private/generated) across {presentModules.size} project modules in the library import graph; used: {used.qsort Name.lt}."

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
