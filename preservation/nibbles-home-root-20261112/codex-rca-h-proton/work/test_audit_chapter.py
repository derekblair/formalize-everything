"""Pure-data regression tests; never starts Lean or changes chapter files."""

import unittest

from audit_chapter import audit, digest, parse_reports, source_scan


class AuditTests(unittest.TestCase):
    source = b"theorem ok : True := True.intro\n#print axioms Demo.ok\n"
    log = b"'Demo.ok' depends on axioms:\n  [propext,\n   Classical.choice, Quot.sound]\n"

    def check(self, source=None, log=None, **record_overrides):
        source = self.source if source is None else source
        log = self.log if log is None else log
        record = {"exit_code": 0, "sha256": digest(source)}
        record.update(record_overrides)
        return audit(source, log, record, "Demo", ["Demo.ok"])

    def test_valid_wrapped_output(self):
        self.assertTrue(self.check()["passed"])

    def test_axiom_free_and_prime_declaration_names(self):
        reports, errors = parse_reports("'Demo.ok\'' does not depend\n on any axioms\n")
        self.assertEqual(reports, {"Demo.ok'": []})
        self.assertFalse(errors)

    def test_nested_comments_strings_raw_strings_and_identifiers(self):
        text = '''/- sorry /- admit -/ axiom -/
-- sorry
def s := "axiom -- sorry /- admit -/"
def r := r##"sorry "# axiom"##
def «admit» := 1
def h' := 2
example := f '' s
example := f ⁻¹' s
example := ∑' n, f n
example := ∏' n, f n
#print axioms Demo.ok
'''
        self.assertEqual(source_scan(text), ([], []))

    def test_actual_tokens_after_comments(self):
        findings, errors = source_scan("/- ignored -/ theorem x : True := by sorry\naxiom y : False")
        self.assertEqual([x["token"] for x in findings], ["sorry", "axiom"])
        self.assertFalse(errors)

    def test_comment_and_string_termination_fail_closed(self):
        for text in ['/- no end', '"no end', 'r#"no end', '«no end']:
            with self.subTest(text=text):
                self.assertTrue(source_scan(text)[1])

    def test_interpolated_code_is_not_silently_ignored(self):
        self.assertTrue(source_scan('def s := s!"{(by sorry : Nat)}"')[1])

    def test_source_placeholder_rejected(self):
        self.assertFalse(self.check(source=b"theorem x : True := by admit")["passed"])

    def test_nonzero_exit_and_boolean_exit_rejected(self):
        for code in [1, -9, False, "0", None]:
            self.assertFalse(self.check(exit_code=code)["passed"])

    def test_wrong_source_or_log_hash_rejected(self):
        self.assertFalse(self.check(sha256="wrong")["passed"])
        self.assertFalse(self.check(log_sha256="wrong")["passed"])

    def test_empty_wrong_family_and_missing_expected_rejected(self):
        for log in [b"", b"'Other.ok' does not depend on any axioms",
                    b"'Demo.other' does not depend on any axioms"]:
            self.assertFalse(self.check(log=log)["passed"])

    def test_unexpected_axioms_inside_and_outside_family_rejected(self):
        for log in [b"'Demo.ok' depends on axioms: [sorryAx]",
                    self.log + b"'Other.bad' depends on axioms: [Custom.bad]"]:
            self.assertFalse(self.check(log=log)["passed"])

    def test_truncated_malformed_and_inconsistent_reports_rejected(self):
        for log in [self.log + b"'Demo.bad' depends on axioms: [",
                    b"'Demo.ok' depends on axioms: [, propext]",
                    self.log + b"'Demo.ok' does not depend on any axioms"]:
            self.assertFalse(self.check(log=log)["passed"])

    def test_cli_error_marker_rejected_even_with_zero_record(self):
        self.assertFalse(self.check(log=self.log + b"file.lean:1:2: error(lean.example): failure")["passed"])


if __name__ == "__main__":
    unittest.main()
