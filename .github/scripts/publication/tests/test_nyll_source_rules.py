"""Regression for the executable closure required by the public source-rules job."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from public_ci import NYLL_SOURCE_RULE_FILES, nyll_source_rule_files, nyll_library_workflow, NYLL_STYLE_BASELINE


class SourceRuleExportTests(unittest.TestCase):
    def test_checker_wrappers_implementations_and_tests_export_together(self):
        files = {path: (path + "\n").encode() for path in NYLL_SOURCE_RULE_FILES}
        files["progress/private.lean"] = b"excluded"
        exported = nyll_source_rule_files(files)
        self.assertEqual(set(exported), set(NYLL_SOURCE_RULE_FILES))
        for path, content in exported.items():
            self.assertIs(content, files[path])

    def test_any_missing_runtime_or_test_dependency_rejects_export(self):
        for missing in NYLL_SOURCE_RULE_FILES:
            with self.subTest(missing=missing), self.assertRaisesRegex(ValueError, "Missing NYLL"):
                nyll_source_rule_files({path: b"source" for path in NYLL_SOURCE_RULE_FILES if path != missing})

    def test_unreviewed_workflow_layout_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "layout changed"):
            nyll_library_workflow("name: Lean\njobs: {}\n")

    def test_public_baseline_render_is_idempotent(self):
        text = "NYLL_STYLE_BASELINE: " + NYLL_STYLE_BASELINE
        self.assertEqual(nyll_library_workflow(text), text)


if __name__ == '__main__':
    unittest.main()
