"""Publication boundaries without Git, network access or Lean execution.

Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0. Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
"""
from __future__ import annotations

from contextlib import ExitStack
import os
import json
from pathlib import Path
import re
import sys
import tempfile
import tomllib
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import public7_sync as core
import public_extract_provenance as provenance


def source_fixture():
    config = '''name = "Nyll"
[[require]]
name = "mathlib"
rev = "pinned-mathlib"
[[lean_lib]]
name = "Nyll"
globs = [
  "Nyll.All",
  "Nyll",
  "Nyll.AbelianVarieties.+",
  "Nyll.JacobianVarieties.+",
]
'''
    texts = {
        'Nyll.lean': 'import Nyll.All\n',
        'Nyll/All.lean': 'import Nyll.AbelianVarieties.All\nimport Nyll.JacobianVarieties.All\n',
        'Nyll/AbelianVarieties/All.lean':
            'import Nyll.AbelianVarieties.Needed\nimport Nyll.AbelianVarieties.Unrelated\n',
        'Nyll/AbelianVarieties/Needed.lean': 'import Mathlib.Init\n',
        'Nyll/AbelianVarieties/Unrelated.lean': '-- unrelated\n',
        'Nyll/JacobianVarieties/All.lean': 'import Nyll.JacobianVarieties.Result\n',
        'Nyll/JacobianVarieties/Result.lean': 'import Nyll.AbelianVarieties.Needed\n',
        'lakefile.toml': config,
        'lake-manifest.json': '{}\n',
        'lean-toolchain': 'lean:test\n',
        'LICENSE': 'retained license\n',
        core.PACKAGE + 'auto_sync.py': '# fixture\n',
        core.PACKAGE + 'public7_sync.py': '# fixture\n',
        core.PACKAGE + 'workflow_templates/auto-sync.yml': '# fixture\n',
    }
    files = {p: text.encode() for p, text in texts.items()}
    source_imports = {core.module(p): [m for m, _, _ in core.imports(text)]
                      for p, text in texts.items() if p.endswith('.lean')}
    graph = {m: [d for d in ds if d == 'Nyll' or d.startswith('Nyll.')]
             for m, ds in source_imports.items()}
    return files, tomllib.loads(config), ['AbelianVarieties', 'JacobianVarieties'], graph, source_imports


class PublicationPolicyTests(unittest.TestCase):
    def setUp(self):
        location = Path(os.environ.get('NYLL_PUBLICATION_TEST_TMP',
                                      str(Path.cwd() / 'tmp' / 'publication-tests')))
        location.mkdir(parents=True, exist_ok=True)
        temp = tempfile.TemporaryDirectory(dir=location)
        self.addCleanup(temp.cleanup)
        self.clones = Path(temp.name)
        self.repo = self.clones / 'JacobianVarieties'
        self.repo.mkdir()
        self.internal = core.INTERNAL_DOCUMENT_PATHS | {
            'AGENTS.md', 'Nyll/JacobianVarieties/AGENTS.md',
            core.PACKAGE + 'AGENTS.md', 'PLAN.md',
            'Nyll/JacobianVarieties/PLAN.md', 'docs/HANDOFF.md', 'docs/ROADMAP.md',
        }
        self.retained = {
            'README.md': b'# Existing public documentation\n',
            'LICENSE': b'retained license\n',
            'Nyll/JacobianVarieties/ATTRIBUTION.md': b'Authors and source license.\n',
            'Nyll/JacobianVarieties/README.md': b'Public mathematical documentation.\n',
            'NOTICE': b'Source notices.\n',
        }
        initial = self.retained | {p: b'Internal work instructions.\n' for p in self.internal}
        initial['Nyll/AbelianVarieties/Unrelated.lean'] = b'-- formerly overbundled\n'
        for rel, data in initial.items():
            path = self.repo / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        self.tracked = set(initial)

    def mocks(self):
        stack = ExitStack()
        stack.enter_context(patch.object(core, 'CLONES', self.clones))
        stack.enter_context(patch.object(core, 'SOURCE', 'a' * 40))
        stack.enter_context(patch.object(core, 'git', side_effect=self.git))
        stack.enter_context(patch.object(core, 'desired_ci', return_value={}))
        stack.enter_context(patch.object(core, 'provenance_files', return_value={}))
        stack.enter_context(patch.object(core, 'managed_provenance_paths', return_value=set()))
        stack.enter_context(patch.object(core, 'readme_for_extract',
                                        return_value=self.retained['README.md']))
        return stack

    def git(self, repo, *args):
        self.assertEqual(repo, self.repo)
        if args == ('status', '--porcelain', '-z'):
            return b''
        if args == ('remote', 'get-url', 'origin'):
            return ('https://github.com/' + core.OWNER + '/JacobianVarieties.git\n').encode()
        if args == ('branch', '--show-current'):
            return b'main\n'
        if args in (('rev-parse', 'HEAD'), ('rev-parse', 'origin/main')):
            return ('b' * 40 + '\n').encode()
        if args == ('ls-files', '-z'):
            return ('\0'.join(sorted(self.tracked)) + '\0').encode()
        self.fail('Unexpected Git operation: ' + repr(args))

    def test_abelian_dependency_is_the_exact_import_closure(self):
        inputs = source_fixture()
        desired, ordered = core.desired_extract(*inputs, ['JacobianVarieties'])
        self.assertEqual(core.DEPTH['AbelianVarieties'], 2)
        self.assertEqual(core.TOPICS[1][-1], 'AbelianVarieties')
        self.assertEqual(ordered, ['AbelianVarieties', 'JacobianVarieties'])
        self.assertEqual({p for p in desired if p.endswith('.lean')}, {
            'Nyll.lean', 'Nyll/All.lean', 'Nyll/AbelianVarieties/Needed.lean',
            'Nyll/JacobianVarieties/All.lean', 'Nyll/JacobianVarieties/Result.lean',
        })
        self.assertEqual(desired['Nyll/All.lean'], b'import Nyll.JacobianVarieties.All\n')
        for path in desired:
            if path.endswith('.lean') and path != 'Nyll/All.lean':
                self.assertEqual(desired[path], inputs[0][path])

    def test_removes_internal_documents_before_the_managed_inventory_existed(self):
        with self.mocks():
            prepared = core.prepare_repository('JacobianVarieties', *source_fixture())
            _, desired, deletes, record = prepared
            self.assertFalse(any(core.is_internal_document(p) for p in desired))
            self.assertTrue(self.internal <= deletes)
            self.assertEqual(deletes - self.internal, {'Nyll/AbelianVarieties/Unrelated.lean'})
            self.assertFalse(set(self.retained) & deletes)
            self.assertTrue(all((self.repo / p).exists() for p in self.internal))
            self.assertEqual(record['depths'], {'AbelianVarieties': 2, 'JacobianVarieties': 3})
            core.apply_prepared([prepared])
        self.assertTrue(record['applied'])
        self.assertTrue(all(not (self.repo / p).exists() for p in self.internal))
        for rel, data in self.retained.items():
            self.assertEqual((self.repo / rel).read_bytes(), data)

    def test_internal_document_in_canonical_package_is_rejected_without_writes(self):
        inputs = source_fixture()
        inputs[0][core.PACKAGE + 'nested/AGENTS.md'] = b'private\n'
        with self.mocks(), self.assertRaisesRegex(ValueError, 'Internal workspace document'):
            core.prepare_repository('JacobianVarieties', *inputs)
        self.assertTrue(all((self.repo / p).exists() for p in self.internal))
        self.assertFalse((self.repo / core.PUBLICATION).exists())


class WorkflowPolicyTests(unittest.TestCase):
    def test_shared_action_pins_match_the_reviewed_updates(self):
        package = Path(__file__).resolve().parents[1]
        # Exported packages carry their templates; canonical NYLL also has the
        # root workflows. Do not require those NYLL-only workflows in extracts.
        paths = list((package / 'ci_templates').glob('*.yml'))
        paths += list((package / 'workflow_templates').glob('*.yml'))
        root = package.parents[2]
        if (root / '.github/workflows/libraries.yml').is_file():
            paths += list((root / '.github/workflows').glob('*.yml'))
        expected = {
            'actions/checkout': '3d3c42e5aac5ba805825da76410c181273ba90b1',
            'actions/cache/restore': '55cc8345863c7cc4c66a329aec7e433d2d1c52a9',
            'actions/cache/save': '55cc8345863c7cc4c66a329aec7e433d2d1c52a9',
            'actions/upload-artifact': 'cf430e030ddbb5b0abf93d22962f4752f3646cd9',
        }
        found = set()
        for path in paths:
            for action, revision in re.findall(r'uses: (actions/[\w/-]+)@([\w.-]+)', path.read_text()):
                if action in expected:
                    with self.subTest(path=path.name, action=action):
                        self.assertEqual(revision, expected[action])
                    found.add(action)
        self.assertEqual(found, set(expected))


class AttributionPolicyTests(unittest.TestCase):
    PATH = 'Nyll/AlgebraicCurves/Divisors/Evaluation.lean'

    def files(self, attribution):
        notice = ('/-\nCopyright (c) 2026 Naganori Yamaguchi (local additions).\n'
                  'Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.\n' +
                  attribution + '\nUpstream NOTICE: ' + provenance.ANTHROPIC +
                  'blob/' + provenance.ANTHROPIC_REV + '/NOTICE\n-/\n')
        return {self.PATH: notice.encode(), provenance.PI1 + 'UPSTREAM.json':
                json.dumps({'local_source_snapshot': {'files': []}}).encode()}

    def test_reviewed_mixed_header_retains_both_original_and_unresolved_credits(self):
        files = self.files('The original local additions have no established direct\n'
            'Anthropic source-file match.\n'
            'Anthropic FLT material was identified by code comparison in the following original\n'
            'modules; their exact source-file correspondence remains unresolved.')
        original = files[self.PATH]
        _, _, anthropic, _ = provenance.selected_records(files, {self.PATH})
        record, = anthropic['AlgebraicCurves']
        self.assertEqual(record['attribution_kind'], 'identified_source_unresolved')
        self.assertEqual(record['upstream_sources'], [])
        self.assertEqual(record['header'], provenance.header(original))
        self.assertEqual(files[self.PATH], original)

    def test_unreviewed_revision_and_ambiguous_notice_remain_rejected(self):
        files = self.files('Anthropic FLT material was identified by code comparison.')
        with self.assertRaisesRegex(ValueError, 'Unclassified Anthropic attribution'):
            provenance.selected_records(files, {self.PATH})
        files = self.files('The source material is identified by code comparison.')
        files[self.PATH] = files[self.PATH].replace(provenance.ANTHROPIC_REV.encode(), b'f' * 40)
        with self.assertRaisesRegex(ValueError, 'new upstream-notice audit'):
            provenance.selected_records(files, {self.PATH})

    def test_historical_library_remark_alone_does_not_assert_source_copying(self):
        for wording in ('no direct Anthropic source-file match is established',
                        'no established direct\nAnthropic source-file match'):
            files = self.files('The original local additions have ' + wording + '.')
            _, _, anthropic, _ = provenance.selected_records(files, {self.PATH})
            self.assertEqual(anthropic, {})

    def test_missing_header_names_the_source_and_is_not_waived(self):
        files = self.files('unused')
        files[self.PATH] = b'import Mathlib.Init\n'
        with self.assertRaisesRegex(ValueError, 'Missing source attribution header: ' + self.PATH):
            provenance.selected_records(files, {self.PATH})


if __name__ == '__main__':
    unittest.main()
