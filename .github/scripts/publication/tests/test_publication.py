"""Regression tests; Git, GitHub writes and Lean are never invoked.

Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0. Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
"""
from __future__ import annotations
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import auto_sync as auto
import public7_sync as core
import public_extract_provenance as provenance

SOURCE = 'a' * 40
PREVIOUS = 'b' * 40
BASE = 'c' * 40
REPOSITORY = auto.OWNER + '/ClassFieldTheory'


def run_record(**overrides):
    row = {'id': 17, 'run_attempt': 1, 'head_sha': SOURCE, 'head_branch': 'main',
           'workflow_id': 9, 'path': '.github/workflows/libraries.yml',
           'event': 'push', 'repository': {'full_name': auto.CANONICAL_REPOSITORY},
           'head_repository': {'full_name': auto.CANONICAL_REPOSITORY},
           'status': 'completed', 'conclusion': 'success'}
    row.update(overrides)
    return row



class PaperReadmeTests(unittest.TestCase):
    PREFIX = 'Nyll/ShimizuYamaguchi26BranchedCoverings/'
    PATHS = set(map(PREFIX.__add__, ('Theorem2Dot3NormalCrossings.lean',
        'Theorem2Dot3SpecialFiberMultiplicity.lean',
        'Geometry/PadicNormalCrossingsQuotient.lean',
        'Geometry/SquareTripleNormalCrossings.lean',
        'Geometry/RationalSectionComplementGeometry.lean'))) | {
        'Nyll/SchemeTheory/ProjectiveSpace/Smooth.lean',
        'Nyll/SchemeTheory/ProjectiveSpace/GenericPoint.lean'}
    TEXT = ('# Papers\n\n### Branched coverings of the projective line over the integers\n\n'
            '| Result | Mathematical content |\n| --- | --- |\n'
            '| [Lemma 2.3: intersection calculations](old23.lean) | Old calculation. |\n'
            '| [Lemma 2.4](old24.lean) | Keep dyadic row verbatim. |\n'
            '| [Proposition 2.5: quadratic quotient](old25.lean) | Old hypothesis. |\n'
            '| [Corollary 2.7: at least seven sections](old27.lean) | Keep quotient row verbatim. |\n\n'
            '## Work still required for complete paper formalizations\n\n'
            '**Branched coverings of the projective line over the integers**\n\n'
            'The full finite-divisor normal-crossing criterion is not yet included.\n\n'
            '## Authorship\n\nKeep this authorship unchanged.\n')

    def test_requires_both_canonical_source_and_selected_membership(self):
        for files, selected in ((dict.fromkeys(self.PATHS, b''), set()),
                                ({}, self.PATHS)):
            self.assertEqual(provenance.branched_coverings_readme(self.TEXT, files, selected),
                             self.TEXT)

    def test_complete_selected_endpoints_preserve_scope_and_existing_rows(self):
        files = dict.fromkeys(self.PATHS, b'')
        result = provenance.branched_coverings_readme(self.TEXT, files, self.PATHS)
        self.assertEqual(provenance.branched_coverings_readme(result, files, self.PATHS), result)
        for row in self.TEXT.splitlines():
            if row.startswith(('| [Lemma 2.4]', '| [Corollary 2.7:')):
                self.assertIn(row, result)
        self.assertEqual(result.split('## Authorship')[1], self.TEXT.split('## Authorship')[1])
        self.assertIn('Observation 2.1: complement geometry', result)
        self.assertIn('special-fibre conditions', result)
        self.assertIn('Theorem2Dot3SpecialFiberMultiplicity.lean', result)
        self.assertIn('Failure of ordinary normal crossings', result)
        self.assertIn('Fundamental-group triviality remains unfinished.', result)
        self.assertIn('Theorem 2.6 remain incomplete.', result)
        self.assertNotIn('full finite-divisor normal-crossing criterion is not yet included', result)

    def test_final_geometry_requires_its_actual_new_providers(self):
        selected = self.PATHS - {'Nyll/SchemeTheory/ProjectiveSpace/GenericPoint.lean',
                                self.PREFIX + 'Theorem2Dot3SpecialFiberMultiplicity.lean'}
        result = provenance.branched_coverings_readme(self.TEXT,
                     dict.fromkeys(self.PATHS, b''), selected)
        self.assertNotIn('[Observation 2.1:', result)
        self.assertNotIn('Theorem2Dot3SpecialFiberMultiplicity.lean', result)
        self.assertIn('are not yet included in this extract.', result)
        self.assertIn('[Lemma 2.3: normal crossings]', result)


class TrustedRunTests(unittest.TestCase):
    def test_accepts_exact_successful_main_push_and_dispatch(self):
        for event in ('push', 'workflow_dispatch'):
            self.assertTrue(auto.trusted_success([run_record(event=event)], SOURCE, 9))

    def test_rejects_each_untrusted_dimension(self):
        variants = {'head_sha': PREVIOUS, 'head_branch': 'topic', 'workflow_id': 10,
            'path': '.github/workflows/other.yml', 'event': 'pull_request',
            'repository': {'full_name': 'other/NYLL'},
            'head_repository': {'full_name': 'other/NYLL'}, 'status': 'in_progress',
            'conclusion': 'failure'}
        for key, value in variants.items():
            with self.subTest(key=key):
                self.assertFalse(auto.trusted_success([run_record(**{key: value})], SOURCE, 9))

    def test_latest_matching_failure_or_pending_supersedes_success(self):
        for row in (run_record(id=18, conclusion='failure'),
                    run_record(id=18, status='queued', conclusion=None),
                    run_record(run_attempt=2, conclusion='failure')):
            self.assertFalse(auto.trusted_success([run_record(), row], SOURCE, 9))

    def test_untrusted_newer_run_cannot_supply_success(self):
        self.assertFalse(auto.trusted_success([run_record(conclusion='failure'),
            run_record(id=18, event='pull_request')], SOURCE, 9))

    def test_main_race_is_rejected(self):
        class API:
            def __init__(self): self.calls = 0
            def main_sha(self, repository):
                self.calls += 1
                return SOURCE if self.calls == 1 else PREVIOUS
            def request(self, path):
                return ({'workflow_runs': [run_record()]} if '/runs?' in path else
                        {'id': 9, 'path': '.github/workflows/libraries.yml'})
        with self.assertRaisesRegex(ValueError, 'changed'):
            auto.verified_main(API())


class LocalTests(unittest.TestCase):
    def setUp(self):
        # The shared workspace never writes test files to the OS temporary folder.
        location = Path(os.environ.get('NYLL_PUBLICATION_TEST_TMP',
                                      str(Path.cwd() / 'tmp' / 'publication-tests')))
        location.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=location)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / 'targets' / 'ClassFieldTheory'
        self.repo.mkdir(parents=True)

    def test_whitelist_and_path_boundaries(self):
        self.assertEqual(auto.repository_name(REPOSITORY), 'ClassFieldTheory')
        for repo in ('else/ClassFieldTheory', auto.OWNER + '/NYLL', REPOSITORY + '/extra'):
            with self.assertRaises(ValueError): auto.repository_name(repo)
        for rel in ('../escape', '/absolute', '.git/config', 'a\\b'):
            with self.assertRaises(ValueError): auto.safe_file(self.repo, rel)
        (self.repo / 'link').symlink_to(self.root)
        with self.assertRaises(ValueError): auto.safe_file(self.repo, 'link/file')

    def test_inventory_detects_modified_managed_file(self):
        (self.repo / 'README.md').write_bytes(b'published')
        path = self.repo / auto.PUBLICATION
        path.parent.mkdir(parents=True)
        value = {'canonical_repository': auto.CANONICAL_REPOSITORY,
                 'repository': REPOSITORY, 'source_commit': PREVIOUS,
                 'managed_hashes': {'README.md': hashlib.sha256(b'published').hexdigest()}}
        path.write_text(json.dumps(value))
        self.assertEqual(auto.previous_snapshot(self.repo, REPOSITORY)['source_commit'], PREVIOUS)
        (self.repo / 'README.md').write_bytes(b'hand edit')
        with self.assertRaisesRegex(ValueError, 'differs'):
            auto.previous_snapshot(self.repo, REPOSITORY)

    def test_rollback_is_skipped_before_checkout_or_pipeline(self):
        calls = []
        def fake_git(repo, *args, **kwargs):
            calls.append(args)
            return subprocess.CompletedProcess(args, 1 if args[0] == 'merge-base' else 0, b'', b'')
        class API:
            token = 'test-only-token'
            def main_sha(self, repository): return BASE
        with patch.object(auto, 'validate_checkout'), \
             patch.object(auto, 'previous_snapshot', return_value={'source_commit': PREVIOUS}), \
             patch.object(auto, 'verified_main', return_value=SOURCE), \
             patch.object(auto, 'git', side_effect=fake_git), \
             patch.object(auto.subprocess, 'run') as process:
            result = auto.execute(REPOSITORY, self.repo, self.root / 'scratch', True, API())
        self.assertEqual(result['status'], 'skipped')
        self.assertIn('does not contain', result['reason'])
        self.assertNotIn('checkout', [args[0] for args in calls])
        process.assert_not_called()

    def test_same_source_is_noop_before_scratch(self):
        class API:
            def main_sha(self, repository): return BASE
        with patch.object(auto, 'validate_checkout'), \
             patch.object(auto, 'previous_snapshot', return_value={'source_commit': SOURCE}), \
             patch.object(auto, 'verified_main', return_value=SOURCE), \
             patch.object(auto, 'git') as git:
            result = auto.execute(REPOSITORY, self.repo, self.root / 'scratch', False, API())
        self.assertEqual(result['status'], 'unchanged')
        self.assertFalse((self.root / 'scratch').exists())
        git.assert_not_called()

    def test_unchanged_extract_keeps_previous_source_and_never_commits(self):
        calls = []
        def fake_git(repo, *args, **kwargs):
            calls.append(args)
            if args[0] == 'checkout':
                path = repo / auto.PACKAGE / 'public7_sync.py'
                path.parent.mkdir(parents=True)
                path.write_text('# same-SHA source owner fixture\n')
            return subprocess.CompletedProcess(args, 0, b'', b'')
        def pipeline(command, **kwargs):
            output = Path(command[command.index('--output') + 1])
            output.mkdir()
            report = {'source_commit': SOURCE, 'repositories': [{'repository': 'ClassFieldTheory',
                      'base_head': BASE, 'unchanged': True, 'changes': [], 'applied': False}]}
            (output / 'public7-plan.json').write_text(json.dumps(report))
            return subprocess.CompletedProcess(command, 0, b'', b'')
        class API:
            token = 'test-only-token'
            def main_sha(self, repository):
                return SOURCE if repository == auto.CANONICAL_REPOSITORY else BASE
        with patch.object(auto, 'validate_checkout'), \
             patch.object(auto, 'previous_snapshot', return_value={'source_commit': PREVIOUS}), \
             patch.object(auto, 'verified_main', return_value=SOURCE), \
             patch.object(auto, 'git', side_effect=fake_git), \
             patch.object(auto.subprocess, 'run', side_effect=pipeline):
            result = auto.execute(REPOSITORY, self.repo, self.root / 'scratch', False, API())
        self.assertEqual(result, {'status': 'unchanged', 'source_commit': PREVIOUS,
                                 'lean_dispatched': False})
        self.assertFalse(any('commit' in args or 'push' in args for args in calls))

    def auto_scenario(self, paths, fail_first_dispatch=False):
        """Exercise the entire publisher with fake Git/API and a pure plan fixture."""
        calls, process_calls = [], []
        state = {'head': BASE, 'remote': BASE, 'posts': 0, 'lean_exists': False}
        commit = 'd' * 40
        changes = [{'path': path, 'action': 'update', 'before_sha256': 'old',
                    'after_sha256': 'new'} for path in paths]
        def fake_git(repo, *args, **kwargs):
            calls.append(args)
            data = b''
            if args[0] == 'checkout':
                path = repo / auto.PACKAGE / 'public7_sync.py'
                path.parent.mkdir(parents=True)
                path.write_text('# fixture\n')
            elif args[0] == 'rev-parse': data = state['head'].encode() + b'\n'
            elif args[0] == 'diff': data = ('\0'.join(paths) + '\0').encode()
            elif 'commit' in args: state['head'] = commit
            elif args[0] == 'push': state['remote'] = commit
            return subprocess.CompletedProcess(args, 0, data, b'')
        def pipeline(command, **kwargs):
            process_calls.append(command)
            output = Path(command[command.index('--output') + 1])
            output.mkdir(exist_ok=True)
            apply = '--apply' in command
            report = {'source_commit': SOURCE, 'repositories': [{'repository': 'ClassFieldTheory',
                'base_head': BASE, 'unchanged': False, 'changes': changes, 'applied': apply}]}
            (output / ('public7-result.json' if apply else 'public7-plan.json')).write_text(json.dumps(report))
            return subprocess.CompletedProcess(command, 0, b'', b'')
        class API:
            token = 'test-only-token'
            def main_sha(self, repository):
                return SOURCE if repository == auto.CANONICAL_REPOSITORY else state['remote']
            def request(self, path, method='GET', body=None):
                if method == 'GET':
                    return {'workflow_runs': [run_record(head_sha=state['remote'],
                        path='.github/workflows/lean.yml', repository={'full_name': REPOSITORY},
                        head_repository={'full_name': REPOSITORY})] if state['lean_exists'] else []}
                state['posts'] += 1
                if fail_first_dispatch and state['posts'] == 1:
                    raise RuntimeError('Simulated dispatch network error')
                self_record = (path, body)
                require_dispatch = '/actions/workflows/lean.yml/dispatches'
                assert path.endswith(require_dispatch) and body == {'ref': 'main'}, self_record
                state['lean_exists'] = True
        return calls, process_calls, state, fake_git, pipeline, API()

    def test_workflow_diff_stops_before_apply(self):
        calls, processes, state, fake_git, pipeline, api = self.auto_scenario(['.github/workflows/lean.yml'])
        with patch.object(auto, 'validate_checkout'), \
             patch.object(auto, 'previous_snapshot', return_value={'source_commit': PREVIOUS}), \
             patch.object(auto, 'verified_main', return_value=SOURCE), \
             patch.object(auto, 'git', side_effect=fake_git), \
             patch.object(auto.subprocess, 'run', side_effect=pipeline):
            result = auto.execute(REPOSITORY, self.repo, self.root / 'scratch', True, api)
        self.assertEqual(result['status'], 'skipped')
        self.assertIn('manual publication', result['reason'])
        self.assertEqual(len(processes), 1)
        self.assertNotIn('--apply', processes[0])
        self.assertFalse(any('commit' in args or 'push' in args for args in calls))

    def test_normal_push_then_one_dispatch(self):
        calls, processes, state, fake_git, pipeline, api = self.auto_scenario(['README.md'])
        with patch.object(auto, 'validate_checkout'), \
             patch.object(auto, 'previous_snapshot', return_value={'source_commit': PREVIOUS}), \
             patch.object(auto, 'verified_main', return_value=SOURCE), \
             patch.object(auto, 'git', side_effect=fake_git), \
             patch.object(auto.subprocess, 'run', side_effect=pipeline):
            result = auto.execute(REPOSITORY, self.repo, self.root / 'scratch', True, api)
        self.assertEqual(result['status'], 'published')
        self.assertEqual(state['posts'], 1)
        self.assertEqual([args for args in calls if args[0] == 'push'],
                         [('push', 'origin', 'HEAD:refs/heads/main')])
        self.assertEqual(len(processes), 2)
        self.assertNotIn('--apply', processes[0])
        self.assertIn('--apply', processes[1])

    def test_push_success_dispatch_failure_recovers_next_same_source_once(self):
        calls, processes, state, fake_git, pipeline, api = self.auto_scenario(['README.md'], True)
        with patch.object(auto, 'validate_checkout'), \
             patch.object(auto, 'previous_snapshot', return_value={'source_commit': PREVIOUS}), \
             patch.object(auto, 'verified_main', return_value=SOURCE), \
             patch.object(auto, 'git', side_effect=fake_git), \
             patch.object(auto.subprocess, 'run', side_effect=pipeline):
            with self.assertRaisesRegex(RuntimeError, 'dispatch'):
                auto.execute(REPOSITORY, self.repo, self.root / 'scratch', True, api)
        self.assertNotEqual(state['remote'], BASE)
        with patch.object(auto, 'validate_checkout'), \
             patch.object(auto, 'previous_snapshot', return_value={'source_commit': SOURCE}), \
             patch.object(auto, 'verified_main', return_value=SOURCE), \
             patch.object(auto, 'git') as git:
            recovered = auto.execute(REPOSITORY, self.repo, self.root / 'next', True, api)
            again = auto.execute(REPOSITORY, self.repo, self.root / 'third', True, api)
        self.assertTrue(recovered['lean_dispatched'])
        self.assertFalse(again['lean_dispatched'])
        self.assertEqual(state['posts'], 2)
        git.assert_not_called()

    def test_existing_failed_lean_is_not_dispatched_again(self):
        class API:
            def request(self, path, method='GET', body=None):
                assert method == 'GET'
                return {'workflow_runs': [run_record(head_sha=BASE, conclusion='failure',
                    path='.github/workflows/lean.yml', repository={'full_name': REPOSITORY},
                    head_repository={'full_name': REPOSITORY})]}
        self.assertFalse(auto.ensure_public_lean(API(), REPOSITORY, BASE, True))

    def test_source_sha_only_manifest_change_is_not_meaningful(self):
        before = {'moduleRows': [{'sha256': 'real-content'}], 'synchronizedFromCommit': PREVIOUS}
        after = dict(before, synchronizedFromCommit=SOURCE, previousSynchronizedFromCommit=PREVIOUS)
        normalize = lambda value: core.normalized_comparison(core.SAWIN_MANIFEST, core.json_bytes(value))
        self.assertEqual(normalize(before), normalize(after))
        after['moduleRows'] = [{'sha256': 'different-content'}]
        self.assertNotEqual(normalize(before), normalize(after))


class ExtractTests(unittest.TestCase):
    def test_daily_schedule_keeps_manual_dispatch(self):
        package = Path(__file__).resolve().parents[1]
        workflow = (package / 'workflow_templates/auto-sync.yml').read_text(encoding='utf-8')
        self.assertIn("cron: '0 0 * * *'", workflow)
        self.assertIn('  workflow_dispatch:', workflow)
        self.assertIn('persist-credentials: false', workflow)
        self.assertIn('actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1', workflow)

    def test_minimal_modules_not_whole_dependency_families(self):
        config = '''name = "Nyll"
[[lean_lib]]
name = "Nyll"
globs = [
  "Nyll.All",
  "Nyll",
  "Nyll.ProCGroups.+",
  "Nyll.ClassFieldTheory.+",
]
'''
        texts = {'Nyll.lean': 'import Nyll.All\n',
            'Nyll/All.lean': 'import Nyll.ProCGroups.All\nimport Nyll.ClassFieldTheory.All\n',
            'Nyll/ProCGroups/All.lean': 'import Nyll.ProCGroups.Needed\nimport Nyll.ProCGroups.Unrelated\n',
            'Nyll/ProCGroups/Needed.lean': 'import Mathlib.Init\n',
            'Nyll/ProCGroups/Unrelated.lean': '-- unrelated\n',
            'Nyll/ClassFieldTheory/All.lean': 'import Nyll.ClassFieldTheory.Result\n',
            'Nyll/ClassFieldTheory/Result.lean': 'import Nyll.ProCGroups.Needed\n',
            'lakefile.toml': config, 'lake-manifest.json': '{}\n', 'lean-toolchain': 'lean:test\n',
            'LICENSE': 'existing license\n'}
        files = {p: text.encode() for p, text in texts.items()}
        imports = {core.module(p): [m for m, _, _ in core.imports(s)]
                   for p, s in texts.items() if p.endswith('.lean')}
        graph = {m: [d for d in ds if d.startswith('Nyll')] for m, ds in imports.items()}
        desired, order = core.desired_extract(files, tomllib.loads(config),
            ['ProCGroups', 'ClassFieldTheory'], graph, imports, ['ClassFieldTheory'])
        self.assertEqual(order, ['ProCGroups', 'ClassFieldTheory'])
        self.assertIn('Nyll/ProCGroups/Needed.lean', desired)
        self.assertNotIn('Nyll/ProCGroups/All.lean', desired)
        self.assertNotIn('Nyll/ProCGroups/Unrelated.lean', desired)
        self.assertEqual(desired['Nyll/All.lean'], b'import Nyll.ClassFieldTheory.All\n')
        self.assertEqual(desired['Nyll/ProCGroups/Needed.lean'], files['Nyll/ProCGroups/Needed.lean'])

    def test_import_parser_masks_nested_comments_and_strings(self):
        text = 'module\n/- outer /- import Wrong.Nested -/ import Wrong.Outer -/\n' \
               'public import Right.Real -- import Wrong.Tail\n' \
               'def s := "import Wrong.String"\n'
        self.assertEqual([m for m, _, _ in core.imports(text)], ['Right.Real'])

    def test_token_never_appears_in_arguments(self):
        with patch.dict(os.environ, {'GIT_CONFIG_COUNT': '2', 'GIT_CONFIG_KEY_1': 'old',
                                     'GIT_CONFIG_VALUE_1': 'old', 'GIT_TRACE_CURL': '1',
                                     'GIT_TRACE': '1', 'GIT_CURL_VERBOSE': '1'}):
            env = auto.auth_environment('fake-test-token')
        self.assertEqual(env['GIT_CONFIG_COUNT'], '1')
        self.assertNotIn('GIT_CONFIG_KEY_1', env)
        self.assertNotIn('GIT_TRACE_CURL', env)
        self.assertNotIn('GIT_TRACE', env)
        self.assertNotIn('GIT_CURL_VERBOSE', env)
        self.assertNotIn('fake-test-token', env['GIT_CONFIG_VALUE_0'])


if __name__ == '__main__':
    unittest.main()
