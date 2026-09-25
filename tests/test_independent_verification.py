import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / '.github/verification'))
import check_main_declarations as main_gate
import verify


class ExportAndNanoDaChecks(unittest.TestCase):
    def test_complete_structural_export_and_unexpected_axiom(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'selected.ndjson'
            rows = [
                {'in': 1, 'str': {'pre': 0, 'str': 'Public'}},
                {'thm': {'name': 1}},
                {'meta': {'lean': {'version': '4.34.0', 'githash': verify.LEAN_REV}}},
            ]
            output.write_text(''.join(json.dumps(row) + '\n' for row in rows))
            inventory = {'Public': {'nameParts': [{'str': 'Public'}]}}
            result = verify.export_coverage(output, inventory, ['Public'])
            self.assertTrue(result['allSelectedPresent'])
            self.assertEqual(result['unexpectedAxiomNameParts'], [])
            rows.insert(2, {'in': 2, 'str': {'pre': 0, 'str': 'Untrusted'}})
            rows.insert(3, {'axiom': {'name': 2}})
            output.write_text(''.join(json.dumps(row) + '\n' for row in rows))
            self.assertTrue(verify.export_coverage(output, inventory, ['Public'])
                            ['unexpectedAxiomNameParts'])

    def test_nanoda_requires_exact_completion_without_skips(self):
        runner = verify.Runner.__new__(verify.Runner)
        runner.selectors = ['Public']
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'nanoda.log'
            log.write_text('Checked 2 declarations with no errors.\n')
            self.assertEqual(runner.check_nanoda(log)['checkedDeclarationsIncludingDependencies'], 2)
            log.write_text('skipping Public\nChecked 2 declarations with no errors.\n')
            with self.assertRaisesRegex(ValueError, 'skipped'):
                runner.check_nanoda(log)


class MainReceiptChecks(unittest.TestCase):
    def test_three_public_theorems_are_required_from_sawin_modules(self):
        contract_path = Path(__file__).resolve().parents[1] / '.github/verification/main-declarations.json'
        contract = json.loads(contract_path.read_text())
        rows = [{'name': item['name'], 'kind': item['kind'],
                 'originModule': item['module'], 'primaryOwner': contract['primaryOwner'],
                 'isSafeKernelRoot': True, 'nonstandardAxioms': [],
                 'hasTransitiveSorry': False} for item in contract['declarations']]
        self.assertEqual(main_gate.check(contract, rows), 3)
        with self.assertRaisesRegex(ValueError, 'Missing main declaration'):
            main_gate.check(contract, rows[:2])
        rows[2]['kind'] = 'definition'
        with self.assertRaisesRegex(ValueError, 'kind/owner changed'):
            main_gate.check(contract, rows)
        rows[2]['kind'] = 'theorem'
        rows[2]['originModule'] = 'SawinTotallyRealTowers.Other'
        with self.assertRaisesRegex(ValueError, 'origin changed'):
            main_gate.check(contract, rows)

    def test_tampered_inventory_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory = root / 'inventory/declarations.jsonl'
            inventory.parent.mkdir()
            inventory.write_text('{"name":"Public"}\n')
            sealed = root / 'sealed-inputs.json'
            sealed.write_text('{}\n')
            names = ['build', 'inventory', 'selection', 'export', 'coverage', 'nanoda', 'replay']
            stages = []
            for name in names:
                log = root / (name + '.log')
                log.write_text('passed\n')
                stages.append({'name': name, 'passed': True, 'exitCode': 0,
                               'log': str(log), 'logSHA256': main_gate.digest(log)})
            artifacts = {str(path.relative_to(root)): main_gate.digest(path)
                         for path in root.rglob('*') if path.is_file()}
            receipt = {'passed': True, 'nanoDaRun': True,
                       'independentKernelCheckPerformed': True,
                       'replay': {'officialKernelReplay': 'PASS'}, 'stages': stages,
                       'artifactsSHA256': artifacts,
                       'sealedInputsSHA256': artifacts['sealed-inputs.json']}
            (root / 'receipt.json').write_text(json.dumps(receipt))
            self.assertEqual(main_gate.sawin_inventory(root)[1], inventory)
            inventory.write_text('{"name":"Tampered"}\n')
            with self.assertRaisesRegex(ValueError, 'Inventory artifact'):
                main_gate.sawin_inventory(root)


if __name__ == '__main__':
    unittest.main()
