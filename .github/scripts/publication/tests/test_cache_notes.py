"""Download instructions and the release-body completion handler."""
import copy
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('cache_notes', Path(__file__).resolve().parents[1] / 'ci_templates/cache-notes.py')
notes = importlib.util.module_from_spec(spec)
spec.loader.exec_module(notes)
REPO = 'owner/library'
SHA = 'a' * 40
EVENT = {'repository': {'full_name': REPO, 'private': False, 'default_branch': 'main'},
         'workflow_run': {'head_repository': {'full_name': REPO}, 'head_branch': 'main',
                          'status': 'completed', 'conclusion': 'success', 'event': 'push',
                          'name': 'Lean', 'path': '.github/workflows/lean.yml', 'head_sha': SHA}}


class CacheNotesTests(unittest.TestCase):
    def test_concise_download_instructions(self):
        text = notes.render(REPO, SHA)
        self.assertTrue(text.startswith(f'Prebuilt Lean cache for `{SHA}` (Linux x86_64).\n'))
        self.assertIn('lake exe cache get\n', text)
        self.assertIn(f'gh release download cache-{SHA}-linux-x86_64 -R {REPO}', text)
        self.assertIn('cache-export.py restore', text)
        self.assertNotIn('successful', text)
        self.assertNotIn('No recompilation', text)
        self.assertEqual(text.count('```'), 2)

    def test_only_matching_release_body_is_changed(self):
        calls = []
        def api(repo, endpoint, token, payload=None):
            calls.append((repo, endpoint, payload))
            return {'id': 7, 'tag_name': notes.identity(REPO, SHA), 'target_commitish': SHA,
                    'draft': False, 'body': 'old text'}
        self.assertTrue(notes.update(EVENT, REPO, 'token', api))
        self.assertEqual(calls[0], (REPO, '/releases/tags/cache-' + SHA + '-linux-x86_64', None))
        self.assertEqual(calls[1], (REPO, '/releases/7', {'body': notes.render(REPO, SHA)}))

    def test_untrusted_or_unsuccessful_events_do_not_call_api(self):
        for key, value in [('head_branch', 'feature'), ('conclusion', 'failure'),
                           ('event', 'pull_request'), ('path', '.github/workflows/other.yml'),
                           ('head_repository', {'full_name': 'fork/library'})]:
            with self.subTest(key=key):
                event = copy.deepcopy(EVENT)
                event['workflow_run'][key] = value
                self.assertFalse(notes.update(event, REPO, 'token', lambda *args: self.fail('Unexpected API call')))
        event = copy.deepcopy(EVENT)
        event['repository']['private'] = True
        self.assertFalse(notes.update(event, REPO, 'token', lambda *args: self.fail('Unexpected API call')))

    def test_missing_release_is_ignored(self):
        self.assertFalse(notes.update(EVENT, REPO, 'token', lambda *args: None))

    def test_other_tag_or_commit_is_never_changed(self):
        for field, value in [('tag_name', 'v1.0.0'), ('target_commitish', 'b' * 40)]:
            calls = []
            def api(*args):
                calls.append(args)
                release = {'id': 7, 'tag_name': notes.identity(REPO, SHA), 'target_commitish': SHA, 'draft': False}
                release[field] = value
                return release
            with self.assertRaisesRegex(ValueError, 'does not match'):
                notes.update(EVENT, REPO, 'token', api)
            self.assertEqual(len(calls), 1)


if __name__ == '__main__':
    unittest.main()
