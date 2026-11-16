/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Boundary
import Cbor.Rfc8949.Boundary.ArrayCountFragment
import Cbor.Rfc8949.Boundary.ChunkCountFragment
import Cbor.Rfc8949.Vectors
import Cbor.Rfc8949.Float
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Build-enforced foundation audit and theorem-family `#print axioms`

Imported from the package root `Cbor.lean` (ticket #34 deliverable 7).

1. **Three-way module-coverage and environment scan (`run_cmd`):**
   Walks the physical package source tree anchored to `<root>/Cbor/Rfc8949/Audit.lean`
   via `IO.FS.realPath`, checks that the discovered `.lean` modules match both
   the imported environment and `expectedModules` (exempting the import-only
   umbrella `Cbor` and this entrypoint `Cbor.Rfc8949.Audit`), and inspects
   every declaration originating in any audited project module — including
   private lemmas and compiler-generated equational/termination helpers —
   failing the build if any declaration introduces a local foundation or
   depends transitively on anything outside `{propext, Classical.choice, Quot.sound}`.
2. **Explicit `#print axioms` across every theorem family** in `Head`, `Item`,
   `Grammar`, `Lex`, `Deterministic`, `Bignum`, `Equiv`, `Duplicates`,
   `Indefinite`, `Boundary`, `Ordering`, and `Vectors`.

Set `CBOR_AUDIT_VERBOSE=1` when elaborating this file to log every audited
declaration individually.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let verbose := (← IO.getEnv "CBOR_AUDIT_VERBOSE") == some "1"
  let expectedModules : Array Name := #[
    `Cbor,
    `Cbor.Rfc8949.Head,
    `Cbor.Rfc8949.Item,
    `Cbor.Rfc8949.Parse,
    `Cbor.Rfc8949.Grammar,
    `Cbor.Rfc8949.Lex,
    `Cbor.Rfc8949.Deterministic,
    `Cbor.Rfc8949.Bignum,
    `Cbor.Rfc8949.Equiv,
    `Cbor.Rfc8949.Duplicates,
    `Cbor.Rfc8949.Indefinite,
    `Cbor.Rfc8949.Boundary,
    `Cbor.Rfc8949.Boundary.ArrayCountFragment,
    `Cbor.Rfc8949.Boundary.ChunkCountFragment,
    `Cbor.Rfc8949.Ordering,
    `Cbor.Rfc8949.Vectors,
    `Cbor.Rfc8949.Vectors.AppendixA,
    `Cbor.Rfc8949.Vectors.AppendixF1,
    `Cbor.Rfc8949.Vectors.Ordering,
    `Cbor.Rfc8949.Float,
    `Cbor.Rfc8949.Float.IEEE754,
    `Cbor.Rfc8949.Float.Narrowing,
    `Cbor.Rfc8949.Float.DataModel,
    `Cbor.Rfc8949.Float.Vectors,
    `Cbor.Rfc8949.Audit
  ]
  let importOnly : Array Name := #[`Cbor, `Cbor.Rfc8949.Audit]
  let isPackageRoot (dir : System.FilePath) : IO Bool := do
    let hasAudit ← (dir / "Cbor" / "Rfc8949" / "Audit.lean").pathExists
    let hasRoot ← (dir / "Cbor.lean").pathExists
    let hasToml ← (dir / "lakefile.toml").pathExists
    return hasAudit && hasRoot && hasToml
  let ownRaw : System.FilePath := (← getFileName)
  let cwd ← IO.currentDir
  let ownPath : System.FilePath ← IO.FS.realPath
    (if ownRaw.isAbsolute then ownRaw else cwd / ownRaw)
  let parent1 := ownPath.parent
  let parent2 := parent1.bind System.FilePath.parent
  unless ownPath.fileName == some "Audit.lean" &&
      (parent1.bind System.FilePath.fileName) == some "Rfc8949" &&
      (parent2.bind System.FilePath.fileName) == some "Cbor" do
    throwError "Foundation audit could not locate package root from {ownPath}"
  let root ← match parent2.bind System.FilePath.parent with
    | some r =>
      if ← isPackageRoot r then pure r
      else throwError "Derived root {r} failed package-root validation"
    | none =>
      throwError "Could not derive package root from {ownPath}"
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
      throwError "Source file outside package root: {file}"
    let rel := comps.drop rootComps.length
    match rel with
    | [] => throwError "Empty relative path for {file}"
    | _ =>
      match (System.FilePath.mk rel.getLast!).fileStem with
      | none => throwError "Missing stem for {file}"
      | some stem =>
        let parts := rel.take (rel.length - 1) ++ [stem]
        let mut m : Name := .anonymous
        for p in parts do
          m := m.mkStr p
        unless discovered.contains m do
          discovered := discovered.push m
  let audited : Array Name := env.header.moduleNames.filter
    (fun m => discovered.contains m)
  for m in discovered do
    unless importOnly.contains m || audited.contains m do
      throwError "Module-inventory mismatch: {m} is on disk but not imported into Audit"
    unless expectedModules.contains m do
      throwError "Module-inventory mismatch: {m} is on disk but absent from expectedModules"
  for m in expectedModules do
    unless importOnly.contains m || audited.contains m do
      throwError "Module-inventory mismatch: expected module {m} is absent from Audit"
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
        throwError "Disallowed local declaration in project: {name}"
      let deps ← collectAxioms name
      for dep in deps do
        unless allowed.contains dep do
          throwError "{name} depends on disallowed foundation {dep}"
        unless used.contains dep do
          used := used.push dep
      if verbose then
        logInfo m!"AUDIT {name}: {deps}"
      count := count + 1
  logInfo m!"CBOR foundation audit passed for {count} declarations across {audited.size} audited modules ({discovered.size} source modules total); used: {used.qsort Name.lt}."

/-! ## Head & Grammar (§3, Appendix B) -/
#print axioms Cbor.Rfc8949.beValue_inj
#print axioms Cbor.Rfc8949.decodeHead_bytes
#print axioms Cbor.Rfc8949.decodeHead_sound
#print axioms Cbor.Rfc8949.RawItem.encode_injective
#print axioms Cbor.Rfc8949.RawItem.encode_prefix_unique
#print axioms Cbor.Rfc8949.parseRaw_eq_some_iff
#print axioms Cbor.Rfc8949.parseWellFormed_eq_some_iff
#print axioms Cbor.Rfc8949.parseWellFormed_encodePreferred
#print axioms Cbor.Rfc8949.Item.WF_iff_exists_encoding

/-! ## Lexicographic, Length-first, CTAP2 byte orders & insertion sort (§4.2.1, §4.2.3) -/
#print axioms Cbor.Rfc8949.lexLt_irrefl
#print axioms Cbor.Rfc8949.lexLt_asymm
#print axioms Cbor.Rfc8949.lexLt_trans
#print axioms Cbor.Rfc8949.lexLt_total
#print axioms Cbor.Rfc8949.lengthFirstLt_irrefl
#print axioms Cbor.Rfc8949.lengthFirstLt_asymm
#print axioms Cbor.Rfc8949.lengthFirstLt_trans
#print axioms Cbor.Rfc8949.lengthFirstLt_total
#print axioms Cbor.Rfc8949.ctap2Lt_irrefl
#print axioms Cbor.Rfc8949.ctap2Lt_asymm
#print axioms Cbor.Rfc8949.ctap2Lt_trans
#print axioms Cbor.Rfc8949.ctap2Lt_total
#print axioms Cbor.Rfc8949.sortedBy_sortBy
#print axioms Cbor.Rfc8949.sortBy_idem

/-! ## Core deterministic encoding & strict round trips (§4.2.1, §5.3.1) -/
#print axioms Cbor.Rfc8949.decodeDeterministic_encodeDeterministic
#print axioms Cbor.Rfc8949.encodeDeterministic_of_decodeDeterministic
#print axioms Cbor.Rfc8949.Item.normalise_normalise
#print axioms Cbor.Rfc8949.encodeDeterministic_normalise

/-! ## Tag-2/3 bignums & I3 boundary characterization (§3.4.3, §4.2.2) -/
#print axioms Cbor.Rfc8949.intValue?_encodeInt
#print axioms Cbor.Rfc8949.encodeInt_uint_iff
#print axioms Cbor.Rfc8949.encodeInt_nint_iff
#print axioms Cbor.Rfc8949.encodeInt_tag2_iff
#print axioms Cbor.Rfc8949.encodeInt_tag3_iff
#print axioms Cbor.Rfc8949.encodeInt_tag2_content
#print axioms Cbor.Rfc8949.encodeInt_tag3_content
#print axioms Cbor.Rfc8949.encodeInt_neg_two_pow_64
#print axioms Cbor.Rfc8949.dossier_form_misclassifies_row13
#print axioms Cbor.Rfc8949.eq_encodeInt_of_isPreferredInt

/-! ## Data-model equivalence — basic & extended (§2, §5.6.1, §3.4.3) -/
#print axioms Cbor.Rfc8949.Item.Equiv.refl
#print axioms Cbor.Rfc8949.Item.Equiv.symm
#print axioms Cbor.Rfc8949.Item.Equiv.trans
#print axioms Cbor.Rfc8949.Item.EquivExt.refl
#print axioms Cbor.Rfc8949.Item.EquivExt.symm
#print axioms Cbor.Rfc8949.Item.EquivExt.trans
#print axioms Cbor.Rfc8949.Item.equiv_map_iff
#print axioms Cbor.Rfc8949.Item.equiv_mapIndef_iff
#print axioms Cbor.Rfc8949.Item.canon_of_isDeterministic
#print axioms Cbor.Rfc8949.Item.equivExt_of_intValue?
#print axioms Cbor.Rfc8949.Item.equivExt_uint_tag2
#print axioms Cbor.Rfc8949.Item.equivExt_nint_tag3
#print axioms Cbor.Rfc8949.Item.equivExt_zero_tag2_empty
#print axioms Cbor.Rfc8949.Item.not_equiv_zero_tag2_empty
#print axioms Cbor.Rfc8949.Item.equivExt_tag2_indef
#print axioms Cbor.Rfc8949.Item.equivExt_tag3_indef
#print axioms Cbor.Rfc8949.Item.equivExt_tag2_leading_zeros
#print axioms Cbor.Rfc8949.Item.equivExt_tag3_leading_zeros

/-! ## Duplicate map keys — strict rejection & first-wins (§5.6) -/
#print axioms Cbor.Rfc8949.decodeStrict_eq_some_iff
#print axioms Cbor.Rfc8949.decodeFirstWins_eq_some_iff
#print axioms Cbor.Rfc8949.decodeFirstWins_noDupKeys
#print axioms Cbor.Rfc8949.decodeFirstWins_of_decodeStrict
#print axioms Cbor.Rfc8949.Item.noDupKeys_of_isDeterministic
#print axioms Cbor.Rfc8949.decodeStrict_of_decodeDeterministic
#print axioms Cbor.Rfc8949.firstWins_indef_bytes_dup
#print axioms Cbor.Rfc8949.firstWins_indef_array_dup
#print axioms Cbor.Rfc8949.firstWins_extended_int_dup
#print axioms Cbor.Rfc8949.zero_vs_tag2_empty_map_split

/-! ## Indefinite-length deflation & twice-amended `< 2^64` hypothesis (§3.2) -/
#print axioms Cbor.Rfc8949.parseWellFormed_deflateIndefinite
#print axioms Cbor.Rfc8949.deflateIndefinite_exists_equiv
#print axioms Cbor.Rfc8949.parseWellFormed_deflateIndefinite_toDefinite
#print axioms Cbor.Rfc8949.deflateIndefinite_definite
#print axioms Cbor.Rfc8949.deflateIndefinite_idem
#print axioms Cbor.Rfc8949.deflateIndefinite_normalise
#print axioms Cbor.Rfc8949.deflateIndefinite_of_definite
#print axioms Cbor.Rfc8949.indefBounded_of_length_lt
#print axioms Cbor.Rfc8949.deflateIndefinite_definite_of_length_lt

/-! ## Boundary counterexamples (Amendments 1 & 2) -/
#print axioms Cbor.Rfc8949.Boundary.array_deflation_counterexample
#print axioms Cbor.Rfc8949.Boundary.no_definite_encoding_arrayItem
#print axioms Cbor.Rfc8949.Boundary.chunk_count_bound_insufficient
#print axioms Cbor.Rfc8949.Boundary.no_definite_encoding_stringItem

/-! ## Map-key ordering profiles (Deliverable 5: §4.2.1, §4.2.3, CTAP2) -/
#print axioms Cbor.Rfc8949.order_core_eq_lengthFirst_same_major_atomic
#print axioms Cbor.Rfc8949.order_core_eq_ctap2_atomic
#print axioms Cbor.Rfc8949.order_core_eq_ctap2_atomic_indefBounded
#print axioms Cbor.Rfc8949.order_core_eq_ctap2_atomic_wire
#print axioms Cbor.Rfc8949.sortBy_core_eq_ctap2_atomic
#print axioms Cbor.Rfc8949.order_core_ne_ctap2_compound
#print axioms Cbor.Rfc8949.not_order_core_eq_ctap2_all
#print axioms Cbor.Rfc8949.order_core_ne_lengthFirst_atomic

/-! ## Conformance vector suites (Deliverable 6: 58 Appendix A, 94 F.1, 8 Ordering) -/
#print axioms Cbor.Rfc8949.Vectors.appendixAFloatFreeVectors_length
#print axioms Cbor.Rfc8949.Vectors.appendixAFloatFreeVectors_excludes_row49
#print axioms Cbor.Rfc8949.Vectors.appendixAFloatFree_all_bidirectional
#print axioms Cbor.Rfc8949.Vectors.appendixF1Vectors_length
#print axioms Cbor.Rfc8949.Vectors.appendixF1Groups_counts
#print axioms Cbor.Rfc8949.Vectors.appendixF1_all_refused
#print axioms Cbor.Rfc8949.Vectors.rfc421CoreKeys_length
#print axioms Cbor.Rfc8949.Vectors.rfc421CoreKeys_bidirectional
#print axioms Cbor.Rfc8949.Vectors.rfc423LengthFirstKeys_bidirectional
#print axioms Cbor.Rfc8949.Vectors.sortBy_core_from_lengthFirst
#print axioms Cbor.Rfc8949.Vectors.sortBy_lengthFirst_from_core
#print axioms Cbor.Rfc8949.Vectors.sortBy_ctap2_from_core_and_lengthFirst
#print axioms Cbor.Rfc8949.Vectors.normalise_map_lengthFirst_to_core

/-! ## Milestone 2: IEEE 754 float wire codecs & Appendix D (`Float.IEEE754`, §3.3, Appendix D) -/
#print axioms Cbor.Rfc8949.FloatWidth.initialByte_eq_major7
#print axioms Cbor.Rfc8949.Float16.ofBits_toBits
#print axioms Cbor.Rfc8949.Float16.toBits_ofBits_of_lt
#print axioms Cbor.Rfc8949.Float32.ofBits_toBits
#print axioms Cbor.Rfc8949.Float32.toBits_ofBits_of_lt
#print axioms Cbor.Rfc8949.Float64.ofBits_toBits
#print axioms Cbor.Rfc8949.Float64.toBits_ofBits_of_lt
#print axioms Cbor.Rfc8949.decodeFloat16_encodeFloat16
#print axioms Cbor.Rfc8949.decodeFloat16_eq_some_iff
#print axioms Cbor.Rfc8949.decodeFloat32_encodeFloat32
#print axioms Cbor.Rfc8949.decodeFloat32_eq_some_iff
#print axioms Cbor.Rfc8949.decodeFloat64_encodeFloat64
#print axioms Cbor.Rfc8949.decodeFloat64_eq_some_iff
#print axioms Cbor.Rfc8949.decodeFloat_encodeFloat
#print axioms Cbor.Rfc8949.decodeFloat_eq_some_iff
#print axioms Cbor.Rfc8949.encodeFloat_prefix_unique
#print axioms Cbor.Rfc8949.encodeFloat_injective
#print axioms Cbor.Rfc8949.decodeFloatPrefix_truncated_f16
#print axioms Cbor.Rfc8949.decodeFloatPrefix_truncated_f32
#print axioms Cbor.Rfc8949.decodeFloatPrefix_truncated_f64
#print axioms Cbor.Rfc8949.Float16.classify_partition
#print axioms Cbor.Rfc8949.Float16.nan_iff_quiet_or_signaling
#print axioms Cbor.Rfc8949.Float32.classify_partition
#print axioms Cbor.Rfc8949.Float64.classify_partition
#print axioms Cbor.Rfc8949.Float64.toIEEEValue_injective
#print axioms Cbor.Rfc8949.decodeFloat16_eq_appendixD

/-! ## Milestone 2: Shortest-float narrowing, deterministic NaN & boundaries (`Float.Narrowing`, §4.1, §4.2.1, §4.2.2) -/
#print axioms Cbor.Rfc8949.widen16To32_toIEEEValue
#print axioms Cbor.Rfc8949.widen32To64_toIEEEValue
#print axioms Cbor.Rfc8949.widen16To64_toIEEEValue
#print axioms Cbor.Rfc8949.Float32.toIEEEValue_injective
#print axioms Cbor.Rfc8949.Float16.toIEEEValue_injective
#print axioms Cbor.Rfc8949.narrow32To16?_eq_some_iff
#print axioms Cbor.Rfc8949.narrow32To16?_eq_none_iff
#print axioms Cbor.Rfc8949.narrow64To32?_eq_some_iff
#print axioms Cbor.Rfc8949.narrow64To32?_eq_none_iff
#print axioms Cbor.Rfc8949.narrow64To16?_eq_some_iff
#print axioms Cbor.Rfc8949.preferredFloat_toIEEEValue
#print axioms Cbor.Rfc8949.isPreferredFloat_iff_eq_preferredFloat
#print axioms Cbor.Rfc8949.preferredFloat_idem
#print axioms Cbor.Rfc8949.encodeFloatPreferred_shortest
#print axioms Cbor.Rfc8949.decodeFloatPreferred_encodeFloatPreferred
#print axioms Cbor.Rfc8949.decodeFloatPreferred_eq_some_iff
#print axioms Cbor.Rfc8949.isDeterministicFloat_iff_eq_canonicalFloatDet
#print axioms Cbor.Rfc8949.canonicalFloatDet_idem
#print axioms Cbor.Rfc8949.encodeFloatDeterministic_nan
#print axioms Cbor.Rfc8949.decodeFloatDeterministic_encodeFloatDeterministic
#print axioms Cbor.Rfc8949.decodeFloatDeterministic_eq_some_iff
#print axioms Cbor.Rfc8949.round64To32_eq_of_narrow64To32?
#print axioms Cbor.Rfc8949.widen32To64_round64To32_eq_iff
#print axioms Cbor.Rfc8949.signed_zero_boundary
#print axioms Cbor.Rfc8949.infinity_boundary
#print axioms Cbor.Rfc8949.nan_payload_and_canonical_boundary
#print axioms Cbor.Rfc8949.subnormal_boundary
#print axioms Cbor.Rfc8949.lossy_narrowing_boundary

/-! ## Milestone 2: Float data-model equivalence, full grammar & F.1 refusal (`Float.DataModel`, §2, §5.6.1) -/
#print axioms Cbor.Rfc8949.FloatEquiv.refl
#print axioms Cbor.Rfc8949.FloatEquiv.symm
#print axioms Cbor.Rfc8949.FloatEquiv.trans
#print axioms Cbor.Rfc8949.floatEquiv_widen16To32
#print axioms Cbor.Rfc8949.floatEquiv_widen32To64
#print axioms Cbor.Rfc8949.floatEquiv_preferredFloat
#print axioms Cbor.Rfc8949.floatEquiv_posZero_negZero
#print axioms Cbor.Rfc8949.floatEquiv_nan_iff
#print axioms Cbor.Rfc8949.canonFloatKey_eq_iff
#print axioms Cbor.Rfc8949.decodeFullHead_bytes
#print axioms Cbor.Rfc8949.decodeFullHead_sound
#print axioms Cbor.Rfc8949.fullHead_complete_vs_truncated
#print axioms Cbor.Rfc8949.parseFullRaw_eq_some_iff
#print axioms Cbor.Rfc8949.FullRawItem.encode_prefix_unique
#print axioms Cbor.Rfc8949.FullRawItem.encode_injective
#print axioms Cbor.Rfc8949.parseFullRaw_of_parseRaw
#print axioms Cbor.Rfc8949.encodeFullDeterministic_of_decodeFullDeterministic
#print axioms Cbor.Rfc8949.FullItem.Equiv.refl
#print axioms Cbor.Rfc8949.FullItem.Equiv.symm
#print axioms Cbor.Rfc8949.FullItem.Equiv.trans
#print axioms Cbor.Rfc8949.FullItem.equiv_float_iff
#print axioms Cbor.Rfc8949.FullItem.not_equiv_float_uint
#print axioms Cbor.Rfc8949.FullItem.not_equiv_float_nint
#print axioms Cbor.Rfc8949.FullItem.not_equiv_float_tag
#print axioms Cbor.Rfc8949.FullItem.not_equiv_float_simple
#print axioms Cbor.Rfc8949.FullItem.equiv_ofItem_iff
#print axioms Cbor.Rfc8949.float_dataModel_equiv_witnesses
#print axioms Cbor.Rfc8949.appendixF1_all_refused_full

/-! ## Milestone 2: 23 Appendix A float vectors & 81-row completeness (`Float.Vectors`, Appendix A) -/
#print axioms Cbor.Rfc8949.Vectors.appendixAFloatVectors_length
#print axioms Cbor.Rfc8949.Vectors.appendixAFloatVectors_preferred_count
#print axioms Cbor.Rfc8949.Vectors.appendixAFloatVectors_nonPreferred_count
#print axioms Cbor.Rfc8949.Vectors.appendixAFloatVectors_rows
#print axioms Cbor.Rfc8949.Vectors.appendixAFloat_all_bidirectional
#print axioms Cbor.Rfc8949.Vectors.appendixAFloatVectors_rows_nodup
#print axioms Cbor.Rfc8949.Vectors.appendixA_complete_81_rows
