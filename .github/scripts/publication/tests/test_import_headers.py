"""Regression checks for lossless, fail-closed publication import headers.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import public7_sync as core
from ci_templates import generate_manifest as audit


class ImportHeaderTests(unittest.TestCase):
    def test_multiline_import_and_comments_preserve_exact_name_offsets(self):
        text = ('/- outer /- import Hidden.Nested -/ -/\n'
                'import\n  /- dependency -/ Nyll.First\n'
                'import -- line comment\n\n Nyll.Second\n'
                'noncomputable section\n'
                'def text := "import Hidden.String"\n'
                'def quoted := `(command|\nimport Hidden.Quotation)\n')
        expected = ['Nyll.First', 'Nyll.Second']
        result = core.imports(text)
        self.assertEqual([name for name, _, _ in result], expected)
        self.assertEqual(result, audit.header_imports(text))
        for name, start, end in result:
            self.assertEqual(text[start:end], name)

    def test_module_prelude_and_supported_modifiers_are_header_tokens(self):
        text = ('\ufeffmodule\nprelude\npublic\nmeta import\n Nyll.Public\n'
                'meta import all Nyll.Internal\nimport Nyll.Plain\n'
                '@[simp] theorem result : True := by trivial\n')
        self.assertEqual([name for name, _, _ in core.imports(text)],
                         ['Nyll.Public', 'Nyll.Internal', 'Nyll.Plain'])

    def test_declaration_body_cannot_create_imports(self):
        for body in ('def raw := r#"\nimport Hidden.Raw\n"#',
                     'def quoted := `(command|\nimport Hidden.Quotation)',
                     'namespace A\n-- import Hidden.Comment\ndef s := "import Hidden.String"'):
            with self.subTest(body=body):
                self.assertEqual(core.imports(body), [])
                self.assertEqual([name for name, _, _ in core.imports('import Nyll.Real\n' + body)],
                                 ['Nyll.Real'])

    def test_malformed_or_unsupported_header_is_rejected(self):
        for text in ('import', 'import\n def result := 1', 'import Nyll.A Nyll.B',
                     'import Nyll.A; import Nyll.B', 'import "Nyll.A"',
                     'import Nyll.α', 'import Nyll.«name»', 'import Nyll.A /- unfinished',
                     'public import Nyll.A', 'module\nprivate import Nyll.A',
                     'module\nmeta public import Nyll.A', 'import all Nyll.A',
                     'module\npublic import all Nyll.A', 'unknown_header import Nyll.A'):
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, 'Lean header'):
                core.imports(text)

    def test_multiline_dependency_is_retained_by_minimal_closure(self):
        from test_publication_policy import source_fixture
        files, cfg, order, graph, source_imports = source_fixture()
        path = 'Nyll/JacobianVarieties/Result.lean'
        files[path] = b'import\n  Nyll.AbelianVarieties.Needed\n'
        module = core.module(path)
        source_imports[module] = [name for name, _, _ in core.imports(files[path].decode())]
        graph[module] = source_imports[module]
        desired, _ = core.desired_extract(files, cfg, order, graph, source_imports,
                                           ['JacobianVarieties'])
        self.assertIn('Nyll/AbelianVarieties/Needed.lean', desired)
        self.assertNotIn('Nyll/AbelianVarieties/Unrelated.lean', desired)
        self.assertEqual(desired[path], files[path])


if __name__ == '__main__':
    unittest.main()
