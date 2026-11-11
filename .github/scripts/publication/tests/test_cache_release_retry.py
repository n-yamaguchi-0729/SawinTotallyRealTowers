"""Failed-job retries may reuse only final caches of this exact workflow run."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

TEMPLATE = Path(__file__).resolve().parents[1] / 'ci_templates/cache-release.yml'
ROOT = Path(__file__).resolve().parents[4]


def retry_script():
    text = TEMPLATE.read_text()
    step = text.split('      - name: Locate final caches from earlier attempts of this run\n', 1)[1]
    body = step.split('        run: |\n', 1)[1].split('      - name:', 1)[0]
    body = '\n'.join(line[10:] for line in body.splitlines())
    return body.split("python3 -B - <<'PY'\n", 1)[1].rsplit('\nPY', 1)[0]


def earlier_keys(attempt):
    with tempfile.TemporaryDirectory() as tmp:
        output = Path(tmp) / 'outputs'
        env = {'GITHUB_RUN_ATTEMPT': str(attempt), 'GITHUB_OUTPUT': str(output),
               'MODERN_CACHE_PREFIX': 'proof-Linux-config-commit-run123',
               'LEGACY_CACHE_PREFIX': 'lean-Linux-X64-config-commit-library-EntryPoint-run123'}
        subprocess.run([sys.executable, '-B', '-c', retry_script()], env=env, check=True)
        result = {}
        lines = iter(output.read_text().splitlines())
        for header in lines:
            kind = header.removesuffix('<<END_CACHE_KEYS')
            result[kind] = []
            for line in lines:
                if line == 'END_CACHE_KEYS':
                    break
                result[kind].append(line)
        return result


class CacheReleaseRetryTests(unittest.TestCase):
    def test_first_attempt_has_no_fallback(self):
        self.assertEqual(earlier_keys(1), {'modern': [], 'legacy': []})

    def test_retry_prefers_latest_prior_final_cache(self):
        keys = earlier_keys(3)
        self.assertEqual(keys['modern'], ['proof-Linux-config-commit-run123-2-all',
                                          'proof-Linux-config-commit-run123-1-all'])
        self.assertEqual(keys['legacy'], [
            'lean-Linux-X64-config-commit-library-EntryPoint-run123-2',
            'lean-Linux-X64-config-commit-library-EntryPoint-run123-1'])
        caches = ['proof-Linux-config-commit-run123-3-library-procgroups',
                  'proof-Linux-config-othercommit-run123-2-all',
                  'proof-Linux-config-commit-run999-2-all',
                  'proof-Linux-config-commit-run123-1-all']
        matches = [cache for key in keys['modern'] for cache in caches if cache.startswith(key)]
        self.assertEqual(matches, ['proof-Linux-config-commit-run123-1-all'])

    def test_live_workflow_and_template_match(self):
        self.assertEqual(TEMPLATE.read_bytes(), (ROOT / '.github/workflows/cache-release.yml').read_bytes())
        text = TEMPLATE.read_text()
        self.assertIn('restore-keys: ${{ steps.earlier.outputs.modern }}', text)
        self.assertIn('restore-keys: ${{ steps.earlier.outputs.legacy }}', text)
        self.assertEqual(text.count('fail-on-cache-miss: true'), 2)
        self.assertIn('${{ github.sha }}-${{ github.run_id }}\n', text)
        self.assertIn('${{ github.sha }}-library-EntryPoint-${{ github.run_id }}\n', text)


if __name__ == '__main__':
    unittest.main()
