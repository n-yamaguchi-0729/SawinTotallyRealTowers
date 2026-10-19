"""README presentation migrations retain substantive sections and source credits."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from public_readme_presentation import INTRODUCTIONS, REPOSITORIES, installation, presentation


class PresentationTests(unittest.TestCase):
    def test_installation_uses_each_distribution_and_the_shared_package_identity(self):
        import re
        import tomllib
        files = {'lakefile.toml': b'name = "Nyll"\n',
                 'lean-toolchain': b'leanprover/lean4:v4.35.0-rc2\n'}
        text = '# Library\n\n## Public API\n\nOld imports.\n\n## Build\n\nOld commands.\n\n## License\n\nCredits.\n'
        for primary, repository in REPOSITORIES.items():
            with self.subTest(repository=repository):
                result = installation(text, primary, files)
                snippet = re.search(r'```toml\n(.*?)\n```', result, re.S)[1]
                dependency = tomllib.loads(snippet)['require'][0]
                self.assertEqual(dependency['name'], 'Nyll')
                self.assertEqual(dependency['git'], 'https://github.com/n-yamaguchi-0729/' + repository + '.git')
                self.assertEqual(re.findall(r'^import (.+)$', result, re.M),
                                 ['Nyll.' + name + '.All' for name in primary])
                self.assertIn('commit your generated lake-manifest.json', result)
                self.assertIn('Credits.', result)
                self.assertEqual(installation(result, primary, files), result)

    def test_all_seven_introductions_are_connected_and_dependency_sections_are_removed(self):
        distribution = ('<!-- nyll-publication:distribution:begin -->\n'
                        'The exact bundled dependency list.\n<!-- nyll-publication:distribution:end -->')
        for primary in INTRODUCTIONS:
            with self.subTest(primary=primary):
                text = ('# Library\n\n[![Lean](badge)](workflow)\n\nOld short sentence.\n\n'
                        '[Old guide](https://example.test).\n\n' + distribution + '\n\n'
                        '## Scope\n\nKeep all hypotheses.\n\n## Included sources\n\nOld inventory.\n\n'
                        '## Public API\n\nKeep imports.\n\n'
                        '## License\n\nKeep attribution.\n')
                result = presentation(text, primary)
                intro = result.split('## Scope')[0]
                self.assertNotIn('Old short sentence', result)
                self.assertIn('[NYLL](', intro)
                self.assertIn('[mathematical guide](', intro)
                self.assertNotIn(distribution, intro)
                for value in ('Keep all hypotheses.', 'Keep imports.', 'Keep attribution.'):
                    self.assertEqual(result.count(value), 1)
                self.assertNotIn('## Included sources', result)
                self.assertNotIn('nyll-publication:distribution', result)
                self.assertNotIn('Old inventory.', result)
                self.assertEqual(presentation(result, primary), result)

    def test_arithmetic_and_geometric_results_share_the_main_results_heading(self):
        text = ('# Library\n\n<!-- nyll-publication:distribution:begin -->\nSources.\n'
                '<!-- nyll-publication:distribution:end -->\n\n## Scope\n\nScope.\n\n'
                '## Genus-zero arithmetic reconstruction\n\nKeep number-field assumptions.\n\n'
                '## Main results\n\nKeep geometric assumptions.\n\n## Public API\n\nImports.\n')
        result = presentation(text, ['AnabelianGeometry'])
        self.assertEqual(result.count('## Main results\n'), 1)
        self.assertIn('### Grothendieck’s conjecture for genus-zero curves over number fields', result)
        self.assertIn('### Geometric fundamental groups', result)
        self.assertIn('Keep number-field assumptions.', result)
        self.assertIn('Keep geometric assumptions.', result)
        self.assertEqual(presentation(result, ['AnabelianGeometry']), result)

    def test_generalized_jacobian_heading_stays_at_the_same_level_on_resync(self):
        text = ('# Library\n\n<!-- nyll-publication:distribution:begin -->\nSources.\n'
                '<!-- nyll-publication:distribution:end -->\n\n## Scope\n\nScope.\n\n'
                '## Main results\n\nFor a smooth curve, retain the hypotheses.\n\n'
                '## Generalized Jacobians\n\nRetain the modulus hypotheses.\n\n'
                '## Public API\n\nImports.\n')
        result = presentation(text, ['JacobianVarieties'])
        self.assertIn('### Zero modulus: ordinary Jacobians\n', result)
        self.assertIn('### General moduli and factorization\n', result)
        self.assertNotIn('#### ', result)
        self.assertEqual(presentation(result, ['JacobianVarieties']), result)
