"""An exact reviewed source transition must preserve historical admission evidence.

Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0. Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
"""
import copy
import hashlib
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from public_sawin import refresh_reviewed_source


class ReviewedSawinSourceTests(unittest.TestCase):
    def setUp(self):
        self.header = b'-- original attribution\n'
        self.previous = self.header + b'theorem proof : True := by simp\n'
        self.current = self.header + b'theorem proof : True := by trivial\n'
        self.sha = lambda data: hashlib.sha256(data).hexdigest()
        self.row = {
            'sourcePath': 'Nyll/Example/Proof.lean',
            'name': 'Nyll.Example.recursiveParent._unsafe_rec',
            'declarationSHA256': 'historical compiled identity',
            'currentSourceSHA256': self.sha(self.previous),
            'historicalBodySHA256': self.sha(self.previous[len(self.header):]),
            'copyrightHeaderByteLength': len(self.header),
            'copyrightHeaderSHA256': self.sha(self.header),
            'canonicalSource': {'commit': 'old admission'},
        }
        self.transition = {
            'path': self.row['sourcePath'], 'old': self.sha(self.previous),
            'new': self.sha(self.current),
            'old_body_sha256': self.row['historicalBodySHA256'],
            'current_body_sha256': self.sha(self.current[len(self.header):]),
            'recursive_parent_declaration_unchanged': True,
            'changed_proofs': ['Nyll.Example.proof'],
        }

    def refresh(self, changes=None):
        with patch('public_sawin.Path.read_text', return_value=json.dumps({
                'reviewedSourceChanges': changes if changes is not None else [self.transition]})):
            refresh_reviewed_source(self.row, self.previous, self.current, 'a' * 40)

    def test_exact_transition_preserves_historical_admission(self):
        before = copy.deepcopy(self.row)
        self.refresh()
        for key in ('name', 'declarationSHA256', 'historicalBodySHA256',
                    'copyrightHeaderSHA256', 'copyrightHeaderByteLength', 'sourcePath'):
            self.assertEqual(self.row[key], before[key])
        self.assertEqual(self.row['currentSourceSHA256'], self.sha(self.current))
        self.assertEqual(self.row['currentBodySHA256'], self.transition['current_body_sha256'])
        self.assertEqual(self.row['canonicalSource']['commit'], 'a' * 40)
        self.assertEqual(self.row['reviewedSourceUpdates'][0]['previousCanonicalSource'],
                         before['canonicalSource'])

    def test_unknown_or_ambiguous_transition_is_rejected_without_mutation(self):
        before = copy.deepcopy(self.row)
        for changes in ([], [self.transition, self.transition]):
            with self.assertRaises(ValueError):
                self.refresh(changes)
            self.assertEqual(self.row, before)

    def test_different_preimage_or_postimage_is_rejected(self):
        for which in ('previous', 'current'):
            with self.subTest(which=which):
                original = getattr(self, which)
                setattr(self, which, original + b'-- unrelated edit\n')
                with self.assertRaises(ValueError):
                    self.refresh()
                setattr(self, which, original)

    def test_changed_header_body_evidence_or_recursive_parent_is_rejected(self):
        before = copy.deepcopy(self.row)
        for key, value in (('old_body_sha256', '0' * 64),
                           ('current_body_sha256', '0' * 64),
                           ('recursive_parent_declaration_unchanged', False)):
            transition = {**self.transition, key: value}
            with self.assertRaises(ValueError):
                self.refresh([transition])
            self.assertEqual(self.row, before)
        self.row['copyrightHeaderSHA256'] = '0' * 64
        with self.assertRaises(ValueError):
            self.refresh()

    def test_replay_cannot_append_another_admission(self):
        self.refresh()
        before = copy.deepcopy(self.row)
        with self.assertRaises(ValueError):
            self.refresh()
        self.assertEqual(self.row, before)


if __name__ == '__main__':
    unittest.main()
