"""Cache distribution rejects mismatched inputs and preserves existing outputs."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

MODULE = Path(__file__).resolve().parents[1] / 'ci_templates/cache-export.py'
spec = importlib.util.spec_from_file_location('cache_export', MODULE)
cache_export = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache_export)


class CacheExportTests(unittest.TestCase):
    def setUp(self):
        compiler = patch.object(cache_export.subprocess, 'check_output', return_value='Lean 4.35.0\n')
        compiler.start()
        self.addCleanup(compiler.stop)
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / 'project'
        self.root.mkdir()
        (self.root / 'Nyll').mkdir()
        (self.root / 'Nyll/A.lean').write_text('def a := 1\n')
        for name in cache_export.CONFIGS:
            (self.root / name).write_text(name)
        self.olean = self.root / '.lake/build/lib/lean/Nyll/A.olean'
        self.olean.parent.mkdir(parents=True)
        self.olean.write_bytes(b'proof artifact')
        self.directory = self.base / 'export'

    def package(self):
        return cache_export.package(self.root, self.directory, 'a' * 40, 'run', 'Lean 4.35.0')

    def test_roundtrip_and_exclusions(self):
        (self.olean.parent / 'A.setup.json').write_text('temporary')
        (self.olean.parent / 'A.o').write_bytes(b'native')
        (self.olean.parent / 'Other.olean').write_bytes(b'stale')
        manifest = self.package()
        self.assertEqual(set(manifest['artifacts']), {'.lake/build/lib/lean/Nyll/A.olean'})
        self.olean.unlink()
        self.assertEqual(cache_export.restore(self.root, self.directory), 1)
        self.assertEqual(self.olean.read_bytes(), b'proof artifact')
        self.assertEqual(cache_export.restore(self.root, self.directory), 0)

    def test_missing_output_cannot_be_published(self):
        self.olean.unlink()
        with self.assertRaisesRegex(ValueError, 'Incomplete final cache'):
            self.package()

    def test_changed_source_rejected(self):
        self.package()
        (self.root / 'Nyll/A.lean').write_text('def a := 2\n')
        with self.assertRaisesRegex(ValueError, 'sources do not match'):
            cache_export.restore(self.root, self.directory)

    def test_conflicting_existing_cache_preserved(self):
        self.package()
        self.olean.write_bytes(b'newer local artifact')
        with self.assertRaisesRegex(ValueError, 'Existing different output preserved'):
            cache_export.restore(self.root, self.directory)
        self.assertEqual(self.olean.read_bytes(), b'newer local artifact')

    def test_archive_corruption_rejected_before_write(self):
        manifest = self.package()
        self.olean.unlink()
        (self.directory / manifest['archives'][0]['name']).write_bytes(b'broken')
        with self.assertRaisesRegex(ValueError, 'checksum/size mismatch'):
            cache_export.restore(self.root, self.directory)
        self.assertFalse(self.olean.exists())

    def test_compiler_mismatch_rejected(self):
        self.package()
        with patch.object(cache_export.subprocess, 'check_output', return_value='Lean 4.36.0\n'):
            with self.assertRaisesRegex(ValueError, 'compiler does not match'):
                cache_export.restore(self.root, self.directory)

    def test_platform_mismatch_rejected(self):
        self.package()
        path = self.directory / 'cache-manifest.json'
        manifest = json.loads(path.read_text())
        manifest['producer']['machine'] = 'a-different-platform'
        path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'platform differs'):
            cache_export.restore(self.root, self.directory)


if __name__ == '__main__':
    unittest.main()
