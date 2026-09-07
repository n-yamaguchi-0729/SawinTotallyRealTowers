import os
from pathlib import Path
import tempfile
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts/verification'))
from verify import Runner

class RuntimePathsRegression(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        base = Path(self.temp.name)
        self.root, self.prefix = base/'package', base/'elan'/'pinned-toolchain'
        self.local = self.root/'.lake'/'build'/'lib'/'lean'
        self.std = self.prefix/'lib'/'lean'
        self.local.mkdir(parents=True); self.std.mkdir(parents=True)
        for p in [self.local/'Module.olean', self.std/'Init.olean',
                  self.prefix/'bin'/'lean', self.prefix/'src'/'lean'/'Lean'/'Replay.lean']:
            p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'fixture')
        self.runner = Runner.__new__(Runner)
        self.runner.root = self.root
        self.runner.git = lambda *_args: ''

    def identity(self, search):
        return {'prefix':str(self.prefix),'searchPath':search,'dependencies':{}}

    def test_real_ci_search_path_accepts_and_seals_pinned_standard_library(self):
        paths = self.runner.runtime_paths(self.identity(str(self.local)+os.pathsep+str(self.std)))
        self.assertIn(self.std/'Init.olean', paths)
        self.assertIn(self.local/'Module.olean', paths)
        self.assertIn(self.prefix/'bin'/'lean', paths)
        self.assertIn(self.prefix/'src'/'lean'/'Lean'/'Replay.lean', paths)

    def test_relative_package_search_path_stays_supported(self):
        paths = self.runner.runtime_paths(self.identity('.lake/build/lib/lean'))
        self.assertIn(self.local/'Module.olean', paths)

    def test_unrelated_external_library_is_still_rejected(self):
        foreign = self.prefix.parent/'untrusted'/'lib'/'lean'
        foreign.mkdir(parents=True)
        with self.assertRaisesRegex(ValueError, 'Unexpected external LEAN_PATH'):
            self.runner.runtime_paths(self.identity(str(foreign)))

    def test_prefix_sibling_is_not_confused_with_standard_library(self):
        with self.assertRaisesRegex(ValueError, 'Unexpected external LEAN_PATH'):
            self.runner.runtime_paths(self.identity(str(self.prefix/'lib'/'lean-extra')))

    def test_package_symlink_to_external_library_is_still_rejected(self):
        external = self.prefix.parent/'other'
        external.mkdir()
        alias = self.root/'.lake'/'external'
        alias.symlink_to(external,target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'Unexpected external LEAN_PATH'):
            self.runner.runtime_paths(self.identity(str(alias)))

if __name__ == '__main__': unittest.main()
