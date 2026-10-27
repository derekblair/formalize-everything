import Bech32.Vectors
import Bech32.EdgeCases
import Bech32.ErrorDetection
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
#print axioms Bech32.gf1024Log_mod_33
#print axioms Bech32.polymod_ne_of_hammingDist_le_four
#print axioms Bech32.verifyChecksum_false_of_data_substitutions_le_four
#print axioms Bech32.verifyChecksum_false_of_substitutions_le_four
#print axioms Bech32.splitLast_eq_some_iff
#print axioms Bech32.decodeChars_eq_some_iff
#print axioms Bech32.decode_ne_same_hrp_of_substitutions_le_four
#print axioms Bech32.decode_encode_ne_same_hrp_of_substitutions_le_four
#print axioms Bech32.decode_eq_none_of_substitutions_le_four
#print axioms Bech32.decode_eq_none_of_alpha_hrp_substitutions_le_four
#print axioms Bech32.decode_eq_none_of_single_substitution
#print axioms Bech32.bech32_q_insertion_undetected
#print axioms Bech32.bech32m_q_insertion_detected
#print axioms Bech32.verifyChecksum_bech32_bech32m_disjoint_of_dist_le_two
#print axioms Bech32.cex1_case_twins_bech32
#print axioms Bech32.cex2b_separator_relocation_bech32
#print axioms Bech32.cex3c_cross_block_hrp_bech32
#print axioms Bech32.cex_length_91_bech32
#print axioms Bech32.cex_cross_variant_distance_three
