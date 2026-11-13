"""Mechanical validator tests; all audit/build messages here are synthetic fixtures."""
import importlib.util
from pathlib import Path
import unittest

PATH = Path(__file__).with_name("check_chapter_gate.py")
spec = importlib.util.spec_from_file_location("gate", PATH)
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class LexerTests(unittest.TestCase):
    def bad(self, source):
        return [x["token"] for x in gate.scan_source(source)["forbidden_tokens"]]

    def test_nested_comments_and_adjacent_real_terms(self):
        self.assertEqual(self.bad("/- sorry /- axiom -/ admit -/ theorem x := by/-x-/sorry"), ["sorry"])
        self.assertEqual(self.bad("-- axiom wrong\ntheorem x := by admit"), ["admit"])

    def test_comment_markers_inside_plain_and_raw_strings(self):
        self.assertEqual(self.bad('def x := "axiom /- sorry -- \\" admit"\ndef y := r##"axiom \\" /- admit"##'), [])

    def test_identifiers_names_characters_and_quotes(self):
        self.assertEqual(self.bad("def sorry' := 3\n#check foo.sorry\n#check «sorry»\n#check `axiom\n#check 'a'"), [])
        self.assertEqual(self.bad("#check `(term| by sorry)"), ["sorry"])

    def test_axiom_declaration_versus_audit_command(self):
        self.assertEqual(self.bad("#print axioms N.good\naxiom added : False"), ["axiom"])
        self.assertEqual(self.bad("axioms added : False"), ["axioms"])
        self.assertEqual(self.bad("theorem t : False := sorryAx _ false"), ["sorryAx"])

    def test_unterminated_and_interpolated_literals_fail_closed(self):
        for source in ('/- open', '"open', 'r##"open', '«open', 's!"{by sorry}"'):
            self.assertTrue(gate.scan_source(source)["lexical_errors"], source)


class AuditTests(unittest.TestCase):
    def test_multiline_and_empty_results(self):
        r = gate.parse_audit("info: file:3:0: 'N.a' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n'N.b' does not depend on any axioms", ["N.a", "N.b"])
        self.assertEqual(r["result_count"], 2)
        for field in ("missing", "unexpected", "duplicates", "disallowed_axioms", "unparsed_axiom_messages"):
            self.assertFalse(r[field], field)

    def test_names_with_prime_and_ansi(self):
        r = gate.parse_audit("\x1b[32m'N.a\'' depends on axioms: []\x1b[0m", ["N.a'"])
        self.assertEqual(r["missing"], [])

    def test_missing_duplicate_unexpected_and_unapproved(self):
        r = gate.parse_audit("'N.a' depends on axioms: [sorryAx]\n'N.a' depends on axioms: []\n'N.extra' depends on axioms: [NewAxiom]", ["N.a", "N.b"])
        self.assertEqual(r["missing"], ["N.b"])
        self.assertEqual(r["duplicates"], ["N.a"])
        self.assertEqual(r["unexpected"], ["N.extra"])
        self.assertEqual(len(r["disallowed_axioms"]), 2)

    def test_truncated_result_fails(self):
        r = gate.parse_audit("'N.a' depends on axioms: [propext,", ["N.a"])
        self.assertTrue(r["unparsed_axiom_messages"])
        self.assertEqual(r["missing"], ["N.a"])

    def test_diagnostics(self):
        for text in ("error: build failed", "a.lean:3:2: error(lean.unknownIdentifier): bad", "warning: declaration uses 'sorry'"):
            self.assertTrue(gate.log_errors(text))
        self.assertFalse(gate.log_errors("warning: unused variable\nBuild completed successfully"))


class EvidenceTests(unittest.TestCase):
    def test_current_pin_files(self):
        self.assertEqual(gate.pin_errors(gate.pins(gate.BOOK)), [])

    def test_pin_mismatch(self):
        self.assertEqual(len(gate.pin_errors({})), 3)

    def test_receipt_hash_status_and_required_inputs(self):
        # Existing test source and script are stable read-only inputs to this unit test.
        source, log = Path(__file__), PATH
        p = gate.pins(gate.BOOK)
        record = dict(schema="lean-chapter-command-receipt-v1", command_exit_status=0,
                      capture_ok=True, source_before=gate.artifact(source),
                      source_after=gate.artifact(source), log=gate.artifact(log),
                      pins_before=p, pins_after=p, command=["synthetic-fixture"],
                      started_at="fixture", finished_at="fixture",
                      inputs_before=[gate.artifact(log)], inputs_after=[gate.artifact(log)])
        self.assertEqual(gate.validate_receipt(record, source, log, p, (log,)), [])
        for field, value in (("command_exit_status", 1), ("source_after", {}), ("log", {}),
                             ("pins_before", {}), ("inputs_after", [])):
            changed = {**record, field: value}
            self.assertTrue(gate.validate_receipt(changed, source, log, p, (log,)), field)


if __name__ == "__main__":
    unittest.main()
