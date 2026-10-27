import Utf8
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Build-enforced, transitive axiom audit over every module whose
source belongs to this package, in the style of the sibling
targets (Merkle's `Checks.lean`, Bech32's `Audit.lean`).

This entrypoint imports the umbrella module `Utf8`, so the
environment it audits is the library's import graph. Declarations
are selected by their originating project module, not just their
public namespace: private helpers and generated
equations/termination declarations are included. No local axiom
declarations are allowed, and dependencies may use only the
standard three axioms below.

Module-coverage guard (three-way inventory): the audit compares
three independently derived sets of project modules.

* DISCOVERED — every `.lean` source file belonging to this
  package, found by walking the package source tree at audit
  time (the library root directory `Utf8/` plus the package-root
  modules such as `Utf8.lean` itself; `.lake` build output is
  excluded), mapped to module names by path. Ownership is the
  source tree, never a module-name prefix.
* AUDITED — the project modules present in this audit's
  environment (`env.header.moduleNames` restricted to the
  discovered inventory).
* EXPECTED — the explicit `expectedModules` inventory below.

The build fails whenever a discovered source module is absent
from the audited environment (present in the tree but not
imported into the audited graph), whenever a discovered or
audited project module is absent from the expected inventory, or
whenever an expected module is missing from the environment. So
every module whose source belongs to this package is audited on
any build in which this audit elaborates — including clean
builds, where the default target compiles every library module,
this entrypoint included.

The package root is resolved from this audit module's own source
position, falling back to an upward search from the working
directory for a directory holding a lakefile together with
`Utf8/Audit.lean`. If no source tree can be located, the audit
fails loudly rather than passing vacuously.

Two inventory entries are import-only and declare nothing: the
umbrella `Utf8` itself, and this audit entrypoint `Utf8.Audit`
(a module cannot appear in its own import environment, so the
entrypoint is accounted for by name rather than by presence).

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
  -- Resolve the package root: primarily from this module's own
  -- source position (`<root>/Utf8/Audit.lean`), falling back to
  -- an upward search from the working directory. A candidate
  -- root must hold a lakefile together with this audit's source.
  let isPackageRoot (dir : System.FilePath) : IO Bool := do
    let hasAudit ← (dir / "Utf8" / "Audit.lean").pathExists
    let hasToml ← (dir / "lakefile.toml").pathExists
    let hasLean ← (dir / "lakefile.lean").pathExists
    return hasAudit && (hasToml || hasLean)
  let mut packageRoot : Option System.FilePath := none
  let ownPath : System.FilePath := (← getFileName)
  if ownPath.isAbsolute then
    match ownPath.parent.bind System.FilePath.parent with
    | some root =>
      if ← isPackageRoot root then
        packageRoot := some root
    | none => pure ()
  if packageRoot.isNone then
    let mut dir : Option System.FilePath := some (← IO.currentDir)
    for _ in [0:16] do
      match dir with
      | none => break
      | some d =>
        if ← isPackageRoot d then
          packageRoot := some d
          break
        dir := d.parent
  let root ← match packageRoot with
    | some r => pure r
    | none => throwError "Axiom audit could not locate the package source tree (no ancestor of the audit module or of the working directory contains a lakefile together with Utf8/Audit.lean); refusing to pass without a source-tree inventory"
  -- DISCOVERED set: every `.lean` source file in the package
  -- source tree (`.lake` build output excluded), mapped to a
  -- module name by its path relative to the package root.
  let mut pending : Array System.FilePath := #[root]
  let mut sourceFiles : Array System.FilePath := #[]
  while !pending.isEmpty do
    let dir := pending.back!
    pending := pending.pop
    for entry in ← dir.readDir do
      let path := entry.path
      if path.fileName == some ".lake" then
        continue
      let md ← path.metadata
      match md.type with
      | .dir => pending := pending.push path
      | .file =>
        if path.extension == some "lean" then
          sourceFiles := sourceFiles.push path
      | .symlink =>
        if ← path.isDir then
          pending := pending.push path
        else if path.extension == some "lean" then
          sourceFiles := sourceFiles.push path
      | _ => pure ()
  let rootComps := root.components
  let mut discovered : Array Name := #[]
  for file in sourceFiles do
    let comps := file.components
    unless comps.take rootComps.length == rootComps do
      throwError "Axiom audit found a source file outside the package root: {file} (package root {root})"
    let rel := comps.drop rootComps.length
    match rel with
    | [] =>
      throwError "Axiom audit could not derive a module name for source file {file}"
    | _ =>
      match (System.FilePath.mk rel.getLast!).fileStem with
      | none =>
        throwError "Axiom audit could not derive a module name for source file {file}"
      | some stem =>
        let parts := rel.take (rel.length - 1) ++ [stem]
        let mut m : Name := .anonymous
        for p in parts do
          m := m.mkStr p
        unless discovered.contains m do
          discovered := discovered.push m
  -- AUDITED set: the project modules present in this
  -- environment, where project ownership is the discovered
  -- source-tree inventory — never a module-name prefix.
  let audited : Array Name := env.header.moduleNames.filter
    (fun m => discovered.contains m)
  -- Three-way comparison. The entrypoint is exempt from the
  -- environment-presence checks: a module cannot appear in its
  -- own import environment.
  for m in discovered do
    unless m == entrypoint || audited.contains m do
      throwError "Axiom audit module-inventory mismatch: source module {m} belongs to this package (present in the package source tree) but is not imported into the audited import graph"
  for m in discovered do
    unless expectedModules.contains m do
      if audited.contains m then
        throwError "Axiom audit module-inventory mismatch: project module {m} is present in the audited import graph but is not in the audit's expected module inventory"
      else
        throwError "Axiom audit module-inventory mismatch: project module {m} is present in the package source tree but is not in the audit's expected module inventory"
  for m in expectedModules do
    unless m == entrypoint || audited.contains m do
      throwError "Axiom audit module-inventory mismatch: expected project module {m} is absent from the audited import graph"
  let mut count : Nat := 0
  let mut used : Array Name := #[]
  let declarations := env.constants.toList.toArray.qsort
    (fun a b => Name.lt a.1 b.1)
  for (name, info) in declarations do
    let projectModule := match env.getModuleIdxFor? name with
      | some idx => audited.contains env.header.moduleNames[idx.toNat]!
      | none => false
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
  logInfo m!"Axiom audit passed for {count} project declarations (including private/generated) across {audited.size} audited project modules; the package source tree holds {discovered.size} project modules, all imported into the audited graph and all present in the expected inventory; used: {used.qsort Name.lt}."

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
