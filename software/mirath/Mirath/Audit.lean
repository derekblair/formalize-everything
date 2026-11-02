import Mirath.DomainChecks
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Audit every `Mirath.*` constant in the imported environment transitively,
and every declaration originating in the listed project modules, including
private/generated declarations with other prefixes. The module inventory
guards the intended import coverage. An axiom outside the standard three, or
a project axiom declaration, fails the default build.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let projectModules := #[`Mirath.Settlement, `Mirath.Model, `Mirath.Totals,
    `Mirath.Distribution, `Mirath.Conservation, `Mirath.Cases, `Mirath.DomainChecks]
  for moduleName in projectModules do
    unless env.header.moduleNames.contains moduleName do
      throwError "Axiom audit is missing expected module {moduleName}"
  let mut count : Nat := 0
  let mut used : Array Name := #[]
  for (name, info) in env.constants.toList do
    let projectDeclaration := match env.getModuleIdxFor? name with
      | some idx => projectModules.contains env.header.moduleNames[idx.toNat]!
      | none => false
    if (`Mirath).isPrefixOf name || projectDeclaration then
      if let .axiomInfo _ := info then
        throwError "Project declares an axiom: {name}"
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
        unless used.contains axiomName do
          used := used.push axiomName
      count := count + 1
  logInfo m!"Axiom audit passed for {count} project declarations across {projectModules.size} modules (including every Mirath.* constant and private/generated declarations); used: {used.qsort Name.lt}."

#print axioms Mirath.distribution_total
#print axioms Mirath.distribution_nonnegative
#print axioms Mirath.distribute?_total
#print axioms Mirath.Cases.husband_two_sisters
