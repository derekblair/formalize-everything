import Sha256Bridge
import Sha256Bridge.Runner
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Build-enforced, transitive axiom audit over every module whose
source belongs to this package, in the style of the sibling
targets (Merkle's `Checks.lean`, Bech32's `Audit.lean`).

This entrypoint imports the umbrella module `Sha256Bridge`, so the
environment it audits is the library's import graph. Declarations
are selected by their originating project module, not just their
public namespace: private helpers and generated
equations/termination declarations are included. This includes the
private-name elaborator in `Upstream` and the compiled vector `Runner`.
The closure follows references into both dependencies, while leaving
unreferenced upstream example declarations outside the audited roots.
No local axiom
declarations are allowed, and dependencies may use only the
standard three axioms below.

Module-coverage guard (three-way inventory): the audit compares
three independently derived sets of project modules.

* DISCOVERED — every `.lean` source file belonging to this
  package, found by walking the package source tree at audit
  time (the library root directory `Sha256Bridge/` plus the package-root
  modules such as `Sha256Bridge.lean` itself; `.lake` build output is
  excluded, as is the exact root `lakefile.lean` build configuration),
  mapped to module names by path. Ownership is the
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

The inventoried tree is anchored to this audit file itself: the
package root is derived from the source path of the audit module
being elaborated — a relative filename is resolved against the
working directory, and the path is then canonicalized with the
operating system's own path resolution (`IO.FS.realPath`), under
which the filesystem follows symbolic links before applying
`..` — so the inventory describes the tree that physically owns
this file, never another checkout found by searching the working
directory's ancestors or by reinterpreting the supplied path
lexically. If the root cannot be derived or fails validation,
the audit fails loudly rather than passing vacuously.

Two inventory entries are import-only and declare nothing: the
umbrella `Sha256Bridge` itself, and this audit entrypoint `Sha256Bridge.Audit`
(a module cannot appear in its own import environment, so the
entrypoint is accounted for by name rather than by presence).

Set `SHA256_BRIDGE_AUDIT_VERBOSE=1` when elaborating this file to print
every declaration's result.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let verbose := (← IO.getEnv "SHA256_BRIDGE_AUDIT_VERBOSE") == some "1"
  -- Expected inventory of project modules. `Sha256Bridge` (the umbrella)
  -- and `Sha256Bridge.Audit` (this entrypoint) are import-only: they
  -- contribute no declarations of their own.
  let expectedModules : Array Name :=
    #[`Sha256Bridge, `Sha256Bridge.Upstream, `Sha256Bridge.Compression,
      `Sha256Bridge.Bytes, `Sha256Bridge.Fold, `Sha256Bridge.Domain,
      `Sha256Bridge.Bridge, `Sha256Bridge.Vectors, `Sha256Bridge.Runner,
      `Sha256Bridge.Audit]
  let entrypoint : Name := `Sha256Bridge.Audit
  -- Resolve the package root from this audit module's own source
  -- position, anchored to the file actually being elaborated.
  -- The reported source filename — absolute under `lake build`,
  -- but possibly relative under a direct `lean` invocation — is
  -- resolved against the working directory when relative, then
  -- canonicalized with the operating system's own path
  -- resolution (`IO.FS.realPath`, the POSIX `realpath`
  -- function), under which the filesystem follows symbolic
  -- links before applying `..`. The result is therefore the
  -- physical file Lean opened, never a lexical reinterpretation
  -- of the supplied path — a purely lexical normalization
  -- mis-derives the root whenever a path reaches this file
  -- through a symlinked directory followed by `..`. The root
  -- is then the resolved file's grandparent directory
  -- (`<root>/Sha256Bridge/Audit.lean`). There is deliberately no search
  -- over ancestors of the working directory or anywhere else:
  -- a directory is the package root only if it owns this very
  -- file, so the inventory below describes the tree the
  -- audited declarations came from, never another checkout.
  -- `realPath` throws when the file cannot be resolved, which
  -- fails this audit rather than letting it pass.
  let isPackageRoot (dir : System.FilePath) : IO Bool := do
    let hasAudit ← (dir / "Sha256Bridge" / "Audit.lean").pathExists
    let hasToml ← (dir / "lakefile.toml").pathExists
    let hasLean ← (dir / "lakefile.lean").pathExists
    return hasAudit && (hasToml || hasLean)
  let ownRaw : System.FilePath := (← getFileName)
  let cwd ← IO.currentDir
  let ownPath : System.FilePath ← IO.FS.realPath
    (if ownRaw.isAbsolute then ownRaw else cwd / ownRaw)
  unless ownPath.fileName == some "Audit.lean" &&
      (ownPath.parent.bind System.FilePath.fileName) == some "Sha256Bridge" do
    throwError "Axiom audit could not locate the package source tree: this audit module's own source path {ownPath} is not of the form <root>/Sha256Bridge/Audit.lean; refusing to pass without a source-tree inventory"
  let root ← match ownPath.parent.bind System.FilePath.parent with
    | some r =>
      if ← isPackageRoot r then
        pure r
      else
        throwError "Axiom audit could not locate the package source tree: the root {r} derived from this audit module's own source path {ownPath} does not contain a lakefile together with Sha256Bridge/Audit.lean; refusing to pass without a source-tree inventory"
    | none =>
      throwError "Axiom audit could not locate the package source tree: this audit module's own source path {ownPath} has no grandparent directory to derive a package root from; refusing to pass without a source-tree inventory"
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
      -- Only this exact package-root file is Lake configuration rather
      -- than a semantic source module. A nested lakefile is not exempt.
      if path == root / "lakefile.lean" then
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
  let mut reduceBoolReach : Nat := 0
  let mut trustCompilerReach : Nat := 0
  let mut sorryReach : Nat := 0
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
      if axioms.contains `Lean.ofReduceBool then
        reduceBoolReach := reduceBoolReach + 1
      if axioms.contains `Lean.trustCompiler then
        trustCompilerReach := trustCompilerReach + 1
      if axioms.contains `sorryAx then
        sorryReach := sorryReach + 1
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
        unless used.contains axiomName do
          used := used.push axiomName
      if verbose then
        logInfo m!"AUDIT {name}: {axioms}"
      count := count + 1
  unless reduceBoolReach == 0 && trustCompilerReach == 0 && sorryReach == 0 do
    throwError "Forbidden-axiom reachability is nonzero"
  logInfo m!"Zero-reachability audit: Lean.ofReduceBool={reduceBoolReach}; Lean.trustCompiler={trustCompilerReach}; sorryAx={sorryReach}."
  logInfo m!"Axiom audit passed for {count} project declarations (including private/generated) across {audited.size} audited project modules; the package source tree holds {discovered.size} project modules, all imported into the audited graph and all present in the expected inventory; used: {used.qsort Name.lt}."

/-- info: 'Sha256Bridge.spec_pad_length_no_wraparound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sha256Bridge.spec_pad_length_no_wraparound
/-- info: 'Sha256Bridge.hash_bits_eq_fips_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sha256Bridge.hash_bits_eq_fips_spec
/-- info: 'Sha256Bridge.hash_bits_eq_spec_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sha256Bridge.hash_bits_eq_spec_unconditional
/-- info: 'Sha256Bridge.hash_toList_eq_spec_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sha256Bridge.hash_toList_eq_spec_bytes
/-- info: 'Sha256Bridge.hash_eq_lean4_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sha256Bridge.hash_eq_lean4_hash
/-- info: 'Sha256Bridge.hash_eq_of_spec_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sha256Bridge.hash_eq_of_spec_bytes
/-- info: 'Sha256Bridge.combine_bits_eq_fips_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sha256Bridge.combine_bits_eq_fips_spec
/-- info: 'Sha256Bridge.combine_toList_eq_spec_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sha256Bridge.combine_toList_eq_spec_bytes
/-- info: 'Sha256Bridge.batch_combine_map_eq_spec_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sha256Bridge.batch_combine_map_eq_spec_bytes
/-- info: 'Sha256Bridge.hash_empty_take28_ne_sha224_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sha256Bridge.hash_empty_take28_ne_sha224_empty
