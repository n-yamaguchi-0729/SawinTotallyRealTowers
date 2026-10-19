"""Exercise the actual CI planner with its distributed header parser, without Lean.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
"""
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ci_templates import generate_manifest
with patch.dict(sys.modules, {'generate_manifest': generate_manifest}):
    from ci_templates import build_stage


class BuildStageTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve()
        sources = {
            'Nyll.Base.Needed': 'theorem needed : True := by trivial\n',
            'Nyll.Target.Result': 'module\npublic meta import\n /- dependency -/ Nyll.Base.Needed\n'
                                  'def text := "import Nyll.Target.All"\n',
            'Nyll.Target.All': 'import -- multiline\n Nyll.Target.Result\n'}
        self.manifest = {'moduleRows': {}}
        self.depths = {'Base': 1, 'Target': 2}
        for name, source in sources.items():
            path = name.replace('.', '/') + '.lean'
            self.manifest['moduleRows'][name] = {'path': path, 'owner': name.split('.')[1]}
            (self.root / path).parent.mkdir(parents=True, exist_ok=True)
            (self.root / path).write_text(source)

    def test_actual_planner_understands_multiline_modified_headers(self):
        self.assertEqual(build_stage.plan(self.root, self.manifest, 2, self.depths),
                         (['Nyll.Target.All'], 2))
        self.assertEqual(build_stage.plan(self.root, self.manifest, 1, self.depths),
                         (['Nyll.Base.Needed'], 1))

    def test_reverse_depth_import_is_rejected(self):
        (self.root / 'Nyll/Base/Needed.lean').write_text('import\n Nyll.Target.Result\n')
        with self.assertRaisesRegex(ValueError, 'Reverse-depth import'):
            build_stage.plan(self.root, self.manifest, 1, self.depths)

    def test_cyclic_frontier_is_rejected(self):
        (self.root / 'Nyll/Target/Result.lean').write_text('import Nyll.Target.All\n')
        with self.assertRaisesRegex(ValueError, 'frontier omits modules'):
            build_stage.plan(self.root, self.manifest, 2, self.depths)

    def test_malformed_header_is_rejected(self):
        (self.root / 'Nyll/Target/Result.lean').write_text('import\n def result := 1\n')
        with self.assertRaisesRegex(ValueError, 'Lean header'):
            build_stage.plan(self.root, self.manifest, 2, self.depths)


if __name__ == '__main__':
    unittest.main()
