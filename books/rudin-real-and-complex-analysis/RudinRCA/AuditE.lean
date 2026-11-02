import RudinRCA.Chapter10
import RudinRCA.Chapter11
import RudinRCA.Chapter12
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Cluster E: transitive axiom audit

The command below checks every `RudinRCA.*` constant in the imported
environment. It also checks every declaration originating in an imported
`RudinRCA.*` module, including private helpers, generated declarations, and
declarations placed outside the public namespace. A locally declared axiom
or a dependency on any axiom other than `propext`, `Classical.choice`, and
`Quot.sound` is a build error.

All three cluster modules must be imported, and the audited declaration set
must be nonempty. These checks prevent an empty import graph from passing
vacuously; they do not establish coverage of the book's numbered nodes.
That coverage is recorded separately in the inventory and progress files.

Set `RUDIN_RCA_AUDIT_VERBOSE=1` to print each declaration's transitive axioms.
This audit defines no mathematical constants or axioms.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let requiredModules :=
    #[`RudinRCA.Chapter10, `RudinRCA.Chapter11, `RudinRCA.Chapter12]
  for chapter in requiredModules do
    unless env.header.moduleNames.contains chapter do
      throwError "Cluster E axiom audit: required chapter {chapter} is not imported"
  let verbose := (← IO.getEnv "RUDIN_RCA_AUDIT_VERBOSE") == some "1"
  let mut count : Nat := 0
  let mut used : Array Name := #[]
  let declarations := env.constants.toList.toArray.qsort
    (fun a b => Name.lt a.1 b.1)
  for (name, info) in declarations do
    let projectModule := match env.getModuleIdxFor? name with
      | some idx => (`RudinRCA).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if (`RudinRCA).isPrefixOf name || projectModule then
      if let .axiomInfo _ := info then
        throwError "Cluster E axiom audit: project declares an axiom {name}"
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Cluster E axiom audit: {name} depends on disallowed axiom {axiomName}"
        unless used.contains axiomName do
          used := used.push axiomName
      if verbose then
        logInfo m!"AUDIT {name}: {axioms}"
      count := count + 1
  if count == 0 then
    throwError "Cluster E axiom audit: no project declarations found; refusing a vacuous pass"
  logInfo m!"Cluster E axiom audit passed for {count} project declarations (including private/generated); Chapters 10, 11, and 12 are imported; used: {used.qsort Name.lt}."
