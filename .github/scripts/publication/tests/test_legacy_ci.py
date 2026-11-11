"""Ensure library splitting preserves mandatory legacy proof verification.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from legacy_ci import legacy_workflow


class LegacyWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.workflow = """name: Lean
on:
  push:
    branches: [main]
jobs:
  build-depth1:
    uses: ./.github/workflows/build-depth.yml
    with:
      depth: 1

  verify:
    if: github.event.repository.private == false
    needs: build-depth1
    steps:
      - run: python3 verify.py --check-all-declarations --nanoda --kernel
"""

    def test_every_library_is_required_before_unmodified_proof_checks(self):
        result = legacy_workflow(self.workflow, ['ProCGroups', 'ClassFieldTheory.LocalFieldTheory', 'ClassFieldTheory'])
        self.assertNotIn('build-depth.yml', result)
        self.assertEqual(result.count('uses: ./.github/workflows/build-library.yml'), 4)
        tail = result.split('  verify:\n', 1)[1].split('\n  publish-cache:\n', 1)[0]
        self.assertIn('needs: [library-procgroups, library-classfieldtheory-localfieldtheory, library-classfieldtheory, library-entrypoint]', tail)
        self.assertIn('    if: github.event.repository.private == false\n', tail)
        self.assertEqual(tail.split('    steps:', 1)[1], self.workflow.split('    steps:', 1)[1])
        self.assertIn('    needs: library-procgroups\n', result)
        self.assertIn('    needs: library-classfieldtheory-localfieldtheory\n', result)

    def test_publication_waits_for_verification_and_is_idempotent(self):
        result = legacy_workflow(self.workflow, ['ProCGroups'])
        self.assertEqual(legacy_workflow(result, ['ProCGroups']), result)
        publish = result.split('  publish-cache:\n', 1)[1]
        self.assertIn('needs: verify', publish)
        self.assertIn("github.ref == 'refs/heads/main'", publish)
        self.assertIn("github.event_name != 'pull_request'", publish)
        self.assertIn('contents: write', publish)
        self.assertIn('cache-kind: legacy', publish)

    def test_unknown_layout_cannot_silently_drop_verification(self):
        with self.assertRaises(ValueError):
            legacy_workflow(self.workflow.replace('  verify:', '  check:'), ['ProCGroups'])

    def test_invalid_or_duplicate_selectors_rejected(self):
        for selectors in ([], ['ProCGroups', 'ProCGroups'], ['CFT; echo unsafe'], ['Foo', 'foo']):
            with self.subTest(selectors=selectors):
                with self.assertRaises(ValueError):
                    legacy_workflow(self.workflow, selectors)

    def test_library_cache_keeps_existing_restoration_prefix(self):
        text = (Path(__file__).resolve().parents[1] / 'ci_templates/build-library.yml').read_text()
        self.assertIn('lean-project-v1-', text)
        self.assertIn('project_cache.py restore', text)
        self.assertIn('project_cache.py seal', text)
        self.assertIn('--library "$LIBRARY_SELECTOR"', text)
        self.assertNotIn('inputs.depth', text)


if __name__ == '__main__':
    unittest.main()
