"""README migration checks; no Lean, Git commands or network operations.

Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0. Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import public_extract_provenance as readme


class ReadmeEndpointTests(unittest.TestCase):
    def test_endpoint_requires_source_selected_membership_and_unique_declaration(self):
        path = 'Nyll/Example/Result.lean'
        source = {path: b'-- source header\n\ntheorem result : True := by trivial\n'}
        link = readme.readme_lean_link(source, {path}, path, 'result')
        self.assertEqual(link, f'[`result`]({path}#L3)')
        for files, selected, name in ((source, set(), 'result'), ({}, {path}, 'result'),
                                       (source, {path}, 'missing')):
            with self.assertRaises(ValueError):
                readme.readme_lean_link(files, selected, path, name)
        with self.assertRaises(ValueError):
            readme.readme_lean_link({path: source[path] * 2}, {path}, path, 'result')

    def test_section_migration_is_idempotent_and_preserves_unowned_content(self):
        text = '# Library\n\n## Scope\n\nOld scope.\n\n## Authorship\n\nKeep attribution.\n'
        updated = readme.readme_section(text, 'Scope', 'scope', 'Precise scope.')
        self.assertEqual(readme.readme_section(updated, 'Scope', 'scope', 'Precise scope.'), updated)
        self.assertEqual(updated.split('## Authorship')[1], text.split('## Authorship')[1])
        with self.assertRaises(ValueError):
            readme.readme_section(text, 'Missing', 'missing', 'Content', before='Absent')

    def test_three_class_field_theories_keep_source_backed_main_results(self):
        base = 'Nyll/ClassFieldTheory/'
        endpoints = {
            'Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocity':
                'finiteAbelianLocalReciprocity',
            'Theorems/LocalClassFieldTheory/FiniteAbelianLocalExistenceOrderIso':
                'finiteAbelianLocalExistence_orderIso',
            'Theorems/LocalClassFieldTheory/ProfiniteLocalReciprocity':
                'profiniteLocalReciprocity',
            'Theorems/GlobalClassFieldTheory/FiniteAbelianGlobalReciprocity':
                'finiteAbelianGlobalReciprocity',
            'Theorems/ConductorsAndRayClassFields/RayClassSubgroupExistence':
                'rayClassSubgroup_existence',
            'Theorems/GlobalClassFieldTheory/TopologicalGlobalReciprocity':
                'topologicalGlobalReciprocity',
            'Theorems/FunctionField/FiniteReciprocity':
                'finiteAbelianGlobalReciprocityQuotient',
            'Theorems/FunctionField/ClassField': 'existsUnique_classField',
            'Definitions/FunctionField/ProfiniteReciprocity': 'profiniteReciprocity'}
        files = {base + path + '.lean':
                 ('theorem ' + name + ' : True := by trivial\n').encode()
                 for path, name in endpoints.items()}
        text = ('# CFT\n\n## Scope\n\nNumber fields.\n\n## Main results\n\n'
                'Old detailed list.\n\n## Incomplete results\n\n'
                'Global function-field class field theory is not included.\n\n'
                '## Public API\n\nKeep API.\n')
        result = readme.current_mathematics_readme(text, files, set(files), ['ClassFieldTheory'])
        self.assertNotIn('not included', result)
        self.assertNotIn('## Function-field class field theory', result)
        self.assertNotIn('## Incomplete results', result)
        self.assertEqual(result.count('## Main results\n'), 1)
        self.assertNotIn('Old detailed list', result)
        for heading in ('Local class field theory', 'Global class field theory: number fields',
                        'Global class field theory: function fields'):
            self.assertIn('### ' + heading + '\n', result)
        for path in files:
            self.assertIn('](' + path + '#L1)', result)
        self.assertIn('identity component', result)
        self.assertIn('usual topology', result)
        self.assertIn('local fields, number fields and function fields', result)
        self.assertIn('import Nyll.ClassFieldTheory.All', result)
        self.assertNotIn('Use all public statements', result)
        for path in files:
            with self.subTest(missing=path), self.assertRaises(ValueError):
                readme.current_mathematics_readme(text, files, set(files) - {path},
                                                ['ClassFieldTheory'])
        self.assertEqual(result, readme.current_mathematics_readme(
            result, files, set(files), ['ClassFieldTheory']))
        with self.assertRaises(ValueError):
            readme.current_mathematics_readme(text, files, set(), ['ClassFieldTheory'])

    @staticmethod
    def paper_endpoints():
        base = 'Nyll/Yamaguchi26AbfaithfulGalois/'
        declarations = {
            'Theorem6Dot6AbsoluteCenter': [
                'absoluteGalois_finiteStepSolvable_centerfree',
                'absoluteGalois_finiteStepSolvable_slim_of_cyclotomic_and_cyclic_extensions'],
            'Theorem6Dot7FieldSlimExamples': [
                'torallyKummerFaithful_finiteStepSolvable_slim',
                'finitelyGenerated_finiteStepSolvable_slim',
                'subpadic_finiteStepSolvable_slim', 'higherLocalField_finiteStepSolvable_slim']}
        return {base + path + '.lean': ''.join(
            'theorem ' + name + ' : True := by trivial\n' for name in names).encode()
                for path, names in declarations.items()}

    def test_private_paper_removed_without_changing_retained_papers_or_attribution(self):
        text = ('# Papers\n\n## Scope\n\nKeep the two public papers.\n\n'
                'The collection also includes an ongoing formalization of\n'
                'the private paper.\n\n## Main results\n\nKeep the public results.\n\n'
                '### Branched coverings of the projective line over the integers\n\n'
                '[Old source](Nyll/ShimizuYamaguchi26BranchedCoverings/All.lean)\n\n'
                '## Incomplete results\n\nKeep public limitations.\n\n'
                '**Branched coverings of the projective line over the integers**\n\n'
                'Old private limitations.\n\n## Public API\n\n```lean\n'
                'import Nyll.Yamaguchi26AbfaithfulGalois.All\n'
                'import Nyll.ShimizuYamaguchi26BranchedCoverings.All\n```\n\n'
                '## Authorship\n\nKeep attribution.\n')
        primary = ['Yamaguchi26AbfaithfulGalois', 'Yamaguchi26SolvableCoverings']
        files = self.paper_endpoints()
        rows = '\n'.join('| [Old](' + path + ') | Old description. |' for path in files)
        text = text.replace('Keep the public results.\n', 'Keep the public results.\n' + rows + '\n')
        result = readme.current_mathematics_readme(text, files, set(files), primary)
        self.assertNotIn('ShimizuYamaguchi', result)
        self.assertNotIn('Branched coverings', result)
        for retained in ('Keep the two public papers.', 'Keep the public results.',
                         'Keep public limitations.', 'Keep attribution.',
                         'import Nyll.Yamaguchi26AbfaithfulGalois.All'):
            self.assertIn(retained, result)
        self.assertEqual(result, readme.current_mathematics_readme(result, files, set(files), primary))
        for claim in ('in any characteristic', 'Slimness additionally assumes',
                      'infinite fields finitely generated over their prime field',
                      'a finitely generated extension of Q_p',
                      'positive-dimensional higher local fields',
                      'every open subgroup has trivial centralizer'):
            self.assertIn(claim, result)
        for path in files:
            with self.subTest(missing=path), self.assertRaises(ValueError):
                readme.current_mathematics_readme(text, files, set(files) - {path}, primary)

    def test_jacobian_conductor_domain_is_not_confused_with_arbitrary_field_factorization(self):
        base = 'Nyll/JacobianVarieties/Generalized/'
        declarations = {
            'GeneralGeometricModulusExistence': ['exists_group_geometricRegularMapHasModulus'],
            'GeneralGroupPicardOneFactorization': ['exists_modulus_unique_picardOneFactor'],
            'GeneralGroupPointedFactorization': ['exists_modulus_unique_pointedGroupFactor'],
            'GeneralGroupLocalSymbolExistence': [
                'existsUnique_group_regularMap_modulus_classification',
                'exists_group_regularMap_localSymbol'],
            'GeneralGroupProductConductor': ['exists_group_regularMap_product_conductors']}
        files = {base + path + '.lean': ''.join(
            'theorem ' + name + ' : True := by trivial\n' for name in names).encode()
                 for path, names in declarations.items()}
        text = ('# JacobianVarieties\n\n## Scope\n\nKeep ordinary Jacobians.\n\n'
                '## Incomplete results\n\nKeep remaining comparisons.\n\n'
                '## Authorship\n\nKeep attribution.\n')
        primary = ['JacobianVarieties']
        result = readme.current_mathematics_readme(text, files, set(files), primary)
        for claim in ('over an arbitrary field', 'algebraically closed field in any characteristic',
                      'extended by the identity outside the open',
                      'coefficientwise maximum', 'pointed form assumes a rational point',
                      'Its support can be smaller than the original boundary',
                      'Keep ordinary Jacobians.', 'Keep remaining comparisons.', 'Keep attribution.'):
            self.assertIn(claim, result)
        self.assertEqual(result, readme.current_mathematics_readme(result, files, set(files), primary))
        for path in files:
            with self.subTest(missing=path), self.assertRaises(ValueError):
                readme.current_mathematics_readme(text, files, set(files) - {path}, primary)

    def test_anabelian_reconstruction_distinguishes_existence_from_strong_isom(self):
        base = 'Nyll/AnabelianGeometry/WeightFiltration/'
        names = {
            'GenusZeroNakamura':
                'exists_schemeIso_of_genusZero_arithmeticFundamentalGroupEquiv',
            'RationalConfigurationNakamura':
                'exists_projectiveTransformation_with_inertia_of_arithmeticFundamentalGroupEquiv'}
        files = {base + path + '.lean':
                 ('theorem ' + name + ' : True := by trivial\n').encode()
                 for path, name in names.items()}
        text = ('# AnabelianGeometry\n\n## Scope\n\nGeometric groups only.\n\n'
                '## Main results\n\nKeep geometric results.\n\n'
                '## Incomplete results\n\nArithmetic reconstruction remains open.\n\n'
                '## Public API\n\nKeep API.\n\n## Authorship\n\nKeep attribution.\n')
        primary = ['AnabelianGeometry']
        result = readme.current_mathematics_readme(text, files, set(files), primary)
        self.assertNotIn('Arithmetic reconstruction remains open', result)
        for name in names.values():
            self.assertIn('`' + name + '`', result)
        for claim in ('geometric genus zero', 'at least\nthree geometric boundary points',
                      'commuting with the maps to G_k', 'are isomorphic over k',
                      'finite models and their descent are constructed',
                      'Realization of a prescribed arithmetic fundamental-group isomorphism',
                      'uniqueness in that correspondence', 'positive genus remain unfinished',
                      'Keep geometric results.', 'Keep API.', 'Keep attribution.'):
            self.assertIn(claim, result)
        self.assertEqual(result, readme.current_mathematics_readme(result, files, set(files), primary))
        with self.assertRaises(ValueError):
            readme.current_mathematics_readme(text, files, {base + 'GenusZeroNakamura.lean'}, primary)

    def test_stacks_inventory_keeps_partial_theorems_out_of_completed_column(self):
        declarations = {
            'EtaleFundamentalGroups/GaloisCategories/MorphismComponents':
                ['exists_component_maps_of_given_coproduct_decompositions'],
            'EtaleFundamentalGroups/FiniteEtale/ProperAlgebraicallyClosedExtension':
                ['pullback_isEquivalence_of_isProper_of_isAlgClosed_constant_extension',
                 'properAlgebraicallyClosedConstantExtensionEquivalence'],
            'EtaleFundamentalGroups/FiniteEtale/ProperSeparablyClosedExtension':
                ['pullback_isEquivalence_of_isProper_of_isSepClosed_constant_extension'],
            'EtaleFundamentalGroups/GeometricFiber/ProperConstantExtensionFundamentalGroup':
                ['fundamentalGroupEquivProperConstantExtension'],
            'EtaleFundamentalGroups/Kummer/AdjoinRoot/StandardTameCodimensionOne':
                ['standardKummerCover_isTamelyRamifiedInCodimensionOne'],
            'EtaleFundamentalGroups/GeometricFiber/StrictHenselianProperFiberSurjective':
                ['fundamentalGroupHom_proper_geometricFiber_surjective_of_strictHenselian'],
            'SchemeTheory/Topology/SpectralClosedRestriction':
                ['exists_clopen_partition_of_connected_closed_intersections'],
            'SchemeTheory/Topology/SpectralClosedSheafRestriction':
                ['sheaf_globalSections_restriction_bijective'],
            'EtaleCohomology/Classical/HenselianLocal':
                ['etaleAbelianCohomology_succ_subsingleton_of_henselianLocalRing'],
            'EtaleCohomology/Sites/FinitePushforwardStalkSurjectivity':
                ['etalePushforwardStalkComparison_isIso'],
            'EtaleCohomology/Classical/FinitePushforward':
                ['etaleAbelianPushforwardFinite_rightDerived_succ_isZero',
                 'etaleCohomologyFinitePushforwardEquiv'],
            'EtaleCohomology/Sites/FiniteBaseChange': ['finiteDirectImageBaseChange_app_isIso'],
            'EtaleCohomology/Sites/ProperGeometricFiberSections':
                ['etalePushforwardGeometricFiberSections_bijective'],
            'EtaleCohomology/Sites/ProperHenselianH0': ['etaleClosedFiber_globalSections_bijective'],
            'EtaleCohomology/Classical/ProperHenselianH1':
                ['etaleClosedFiber_cohomology_one_injective'],
            'EtaleCohomology/Trace/Perfect': ['perfectComplexTrace'],
            'EtaleCohomology/Frobenius/ModuleConstantFieldAction':
                ['finiteFieldFrobeniusCohomology_pow_eq_constantFieldAction']}
        files = {'Nyll/' + path + '.lean': ''.join(
            'theorem ' + name + ' : True := by trivial\n' for name in names).encode()
                 for path, names in declarations.items()}
        entries = [('58.3.7', '0BN0'), ('58.9.3', '0A49'), ('58.31.4', '0EYF'),
                   ('58.30.1', '0C0P'), ('59.82.3', '0CAM'), ('59.82.4', '09ZG'),
                   ('59.55.1', '03QO'), ('59.55.2', '03QP'), ('59.55.3', '0959'),
                   ('59.91.4', '0A3T')]
        text = '# Étale\n\n' + '\n'.join(
            f'| [{number} Section](https://stacks.math.columbia.edu/tag/{tag}) | — | '
            f'[{number}](https://stacks.math.columbia.edu/tag/{tag}) |'
            for number, tag in entries) + '\n\n## Public API\n\nKeep API.\n'
        result = readme.current_stacks_readme(text, files, set(files))
        for number, tag in entries:
            row = next(line for line in result.splitlines() if line.startswith('| [' + number + ' '))
            columns = row.split(' | ')
            location = 2 if tag in {'03QO', '0959', '0A3T', '0C0P'} else 1
            self.assertIn('[' + number + ']', columns[location])
            self.assertNotIn('[' + number + ']', columns[3 - location])
        self.assertIn('Global algebraization', result)
        self.assertIn('the general specialization map is not yet constructed', result)
        self.assertIn('of separably closed fields', result)
        self.assertIn('actual continuous fundamental-group isomorphism', result)
        self.assertIn('coefficient-linear comparison', result)
        self.assertIn('commutes with arbitrary base change', result)
        for path in ('Nyll/EtaleFundamentalGroups/FiniteEtale/ProperSeparablyClosedExtension.lean',
                     'Nyll/EtaleFundamentalGroups/GeometricFiber/ProperConstantExtensionFundamentalGroup.lean',
                     'Nyll/EtaleCohomology/Classical/FinitePushforward.lean'):
            with self.subTest(missing=path), self.assertRaises(ValueError):
                readme.current_stacks_readme(text, files, set(files) - {path})
        self.assertIn('are not yet proved', result)
        self.assertEqual(result, readme.current_stacks_readme(result, files, set(files)))

    def test_legacy_links_resolve_declaration_and_relocated_module(self):
        path = 'Nyll/SchemeTheory/RingTheory/Dimension/PrimeContainingAtHeightOne.lean'
        name = 'exists_prime_containing_ringKrullDim_localization_eq_one'
        files = {path: ('\n\ntheorem ' + name + ' : True := by trivial\n').encode()}
        old = '[Lean](Nyll/SchemeTheory/RingTheory/PrimeContainingAtHeightOne.lean#L170)'
        result = readme.refresh_stacks_lean_links(old, files, {path})
        self.assertEqual(result, f'[`{name}`]({path}#L3)')
        self.assertEqual(result, readme.refresh_stacks_lean_links(result, files, {path}))


if __name__ == '__main__':
    unittest.main()
