#!/usr/bin/env python3
"""Regression checks for the Python annotation/mirror boundary.

This is not the proof: the Lean corpus audit checks all actual verdicts.
These checks exercise missing data and malformed/unsupported readings that
should never acquire a favorable default. Uses only Python's standard library.
"""
import unittest
from unittest.mock import patch

from generate import IAMB, annotate, realize, scan_verdict, scans


class MeterBoundaryChecks(unittest.TestCase):
    def test_strict_and_each_license(self):
        self.assertEqual(scan_verdict({'stress': IAMB, 'elision': None}),
                         (True, True, []))
        examples = [
            ([True, False] + IAMB[2:], None, 'INITIAL_TROCHAIC_INVERSION'),
            (IAMB + [False], None, 'FEMININE_ENDING'),
            ([False, False] + IAMB[2:], None, 'PYRRHIC_SUBSTITUTION'),
            ([True, True] + IAMB[2:], None, 'SPONDAIC_SUBSTITUTION'),
            ([False] + IAMB, 0, 'UNSTRESSED_ELISION'),
        ]
        for raw, elision, license_name in examples:
            with self.subTest(license=license_name):
                strict, licensed, names = scan_verdict({'stress': raw, 'elision': elision})
                self.assertFalse(strict)
                self.assertTrue(licensed)
                self.assertIn(license_name, names)

    def test_bad_readings_fail_and_receive_no_licenses(self):
        examples = [
            ([], None),
            (IAMB[:8], None),
            (IAMB + [True], None),
            (IAMB + [False, False], None),
            (IAMB[:2] + [True, False] + IAMB[4:], None),
            ([True] * 10, None),
            ([True] + IAMB, 0),
            (IAMB, 99),
            (IAMB, -1),
        ]
        for raw, elision in examples:
            with self.subTest(raw=raw, elision=elision):
                self.assertEqual(scan_verdict({'stress': raw, 'elision': elision}),
                                 (False, False, []))

    def test_realization_preserves_fixed_stress_and_count(self):
        masks = [None, False, True, None, False, None]
        raw = realize(masks)
        self.assertEqual(raw, [False, False, True, True, False, True])
        self.assertEqual(len(raw), len(masks))

    def test_only_fixed_weak_elision_is_eligible(self):
        for invalid_index in [-1, 0, 1, 3, 99]:
            with self.subTest(index=invalid_index):
                self.assertEqual(len(scans([None, True, False], [invalid_index])), 1)
        candidate = scans([None, True, False, None], [2])[1]
        self.assertEqual(candidate, {'stress': [False, True, False, False], 'elision': 2})
        self.assertEqual(scans([], [0]), [])


class AnnotationBoundaryChecks(unittest.TestCase):
    @staticmethod
    def fake_lookup(token):
        phones = {'rose': ['R', 'OW1', 'Z'],
                  'heaven': ['HH', 'EH1', 'V', 'AH0', 'N']}.get(token)
        return (phones, 'test fixture') if phones is not None else None

    def test_missing_interior_word_cannot_disappear_from_meter(self):
        with patch('generate.resolve', self.fake_lookup):
            result = annotate('rose unknown rose')
        self.assertEqual(result['unknown'], ['unknown'])
        self.assertEqual(result['masks'], [])
        self.assertEqual(result['scans'], [])
        self.assertFalse(result['strict'])
        self.assertFalse(result['licensed'])
        self.assertEqual(result['rhyme'], 'OW Z')

    def test_missing_end_word_also_has_no_rhyme(self):
        with patch('generate.resolve', self.fake_lookup):
            result = annotate('rose unknown')
        self.assertIsNone(result['rhyme'])
        self.assertEqual(result['scans'], [])

    def test_elision_index_counts_syllables_and_text_is_preserved(self):
        original = 'rose heaven rose'
        with patch('generate.resolve', self.fake_lookup):
            result = annotate(original)
        self.assertEqual(result['text'], original)
        self.assertEqual(result['masks'], [None, True, False, None])
        self.assertEqual(result['eligible_elisions'], [2])
        self.assertEqual(len(result['scans']), 2)

    def test_editorial_alias_preserves_source_and_does_not_guess_other_words(self):
        from pronunciations import resolve
        original = 'The dear respose for limbs with travel tired;'
        result = annotate(original)
        self.assertEqual(result['text'], original)
        self.assertEqual(result['words'][2]['token'], 'respose')
        self.assertEqual(result['words'][2]['phonemes'], resolve('repose')[0])
        self.assertIn('Folger', result['words'][2]['derivation'])
        self.assertIsNone(resolve('respoze'))

    def test_empty_text_cannot_pass(self):
        result = annotate('')
        self.assertEqual(result['scans'], [])
        self.assertIsNone(result['rhyme'])
        self.assertFalse(result['strict'])
        self.assertFalse(result['licensed'])


if __name__ == '__main__':
    unittest.main()
