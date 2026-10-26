import Bech32.Vectors
import Bech32.EdgeCases
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Every public declaration in this project is audited transitively, including
the executable definitions, general proofs, and individual vector theorems.
An unexpected axiom is a build error. This command creates no logical axioms.
-/

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if (`Bech32).isPrefixOf name then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
      count := count + 1
  logInfo m!"Axiom audit passed for {count} Bech32 declarations."

#print axioms Bech32.decode_encode
#print axioms Bech32.decode_encode_bech32
#print axioms Bech32.decode_encode_bech32m
#print axioms Bech32.decode_encode_normalized
#print axioms Bech32.verifyChecksum_createChecksum
#print axioms Bech32.verifyChecksum_iff_createChecksum
