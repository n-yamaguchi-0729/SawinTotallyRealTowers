import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1] / '.github/verification'
sys.path.insert(0, str(SCRIPTS))
import check_source_closure as source
import verify

class SourceClosureTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.rows = {}
        self.put('Proof.Base', 'theorem one : True := True.intro\n')
        self.put('Proof.Entry', 'import Proof.Base\nexample : True := one\n')
        self.manifest = {'roots': ['Proof.Entry'], 'moduleRows': self.rows}

    def put(self, module, text):
        rel = 'Lean4/' + module.replace('.', '/') + '.lean'; p = self.root/rel
        p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
        self.rows[module] = {'owner': module.split('.')[0], 'path': rel,
                            'sha256': source.digest(p), 'imports': source.source_imports(text)}

    def test_valid_exact_closure(self):
        self.assertEqual(source.audit_rows(self.root, self.manifest)['moduleCount'], 2)

    def test_missing_file_rejected(self):
        (self.root/'Lean4/Proof/Base.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'Missing'): source.audit_rows(self.root, self.manifest)

    def test_source_mutation_rejected(self):
        (self.root/'Lean4/Proof/Base.lean').write_text('theorem false_claim : False := by sorry\n')
        with self.assertRaisesRegex(ValueError, 'SHA'): source.audit_rows(self.root, self.manifest)

    def test_extra_unreachable_module_rejected(self):
        self.put('Proof.Extra', 'example : True := True.intro\n')
        with self.assertRaisesRegex(ValueError, 'outside'): source.audit_rows(self.root, self.manifest)

    def test_missing_local_import_rejected(self):
        self.put('Proof.Entry', 'import Proof.Missing\n')
        with self.assertRaisesRegex(ValueError, 'Unresolved'): source.audit_rows(self.root, self.manifest)

    def test_cycle_rejected(self):
        self.put('Proof.Base', 'import Proof.Entry\n')
        with self.assertRaisesRegex(ValueError, 'cycle'): source.audit_rows(self.root, self.manifest)

    def test_aggregate_in_import_closure_accepted(self):
        self.put('Proof.All', 'import Proof.Base\n')
        self.put('Proof.Entry', 'import Proof.All\n')
        self.assertEqual(source.audit_rows(self.root, self.manifest)['moduleCount'], 3)

    def test_forged_path_rejected(self):
        self.rows['Proof.Base']['path'] = '../Base.lean'
        with self.assertRaisesRegex(ValueError, 'path/owner'): source.audit_rows(self.root, self.manifest)

    def test_hole_rejected_even_with_updated_hash(self):
        self.put('Proof.Base', 'example : True := by sorry\n')
        with self.assertRaisesRegex(ValueError, 'placeholder'): source.audit_rows(self.root, self.manifest)

    def test_nested_comments_and_strings_are_not_imports(self):
        text = '/- import Fake.A /- import Fake.B -/ -/\nimport Mathlib.Algebra.Group.Defs\ndef s := "import Fake.C"\n'
        self.assertEqual(source.source_imports(text), ['Mathlib.Algebra.Group.Defs'])

    def test_late_import_rejected(self):
        with self.assertRaisesRegex(ValueError, 'after'):
            source.source_imports('def x := 1\nimport Mathlib.Algebra.Group.Defs\n')

class InventoryTests(unittest.TestCase):
    def setUp(self):
        mod = source.ENTRY
        self.manifest = {'roots': [mod], 'moduleRows': {mod: {
            'owner': 'SawinTotallyRealTowers', 'path': 'Lean4/'+mod.replace('.', '/')+'.lean',
            'sha256': 'a'*64}}}
        self.baseline = {'allowedPartialDeclarations': []}
        self.summary = {'auditPassed':True,'moduleCoverageExact':True,'importRoots':[mod],
            'importLevel':'private','importTrustLevel':0,'primaryModuleCount':1,
            'loadedPrimaryModuleCount':1,'missingRequestedModules':[],'missingRootModules':[],
            'repairedModuleCount':0,'allowedAxioms':list(verify.ALLOWED),
            'owners':{'SawinTotallyRealTowers':{'requestedModules':1,'loadedModules':1,
                       'moduleCoverageExact':True}},'allSelected':{'declarations':1}}
        self.modules = [{'module':mod,'path':self.manifest['moduleRows'][mod]['path'],
                         'primaryOwner':'SawinTotallyRealTowers','isLoaded':True}]
        self.row = {'name':source.MAIN,'originModule':mod,'primaryOwner':'SawinTotallyRealTowers',
            'kind':'theorem','isPrimary':True,'nameToStringRoundTrip':True,'nonstandardAxioms':[],
            'axioms':list(verify.ALLOWED),'hasTransitiveSorry':False,'typeHasSorry':False,
            'valueHasSorry':False,'hasSyntheticSorry':False,'hasNonSyntheticSorry':False,
            'isUnsafe':False,'isPartial':False,'isSafeKernelRoot':True,
            'nameParts':[{'str':'example'}]}

    def check(self, rows=None, source_root=Path('.')):
        return verify.validate_inventory_data(self.summary, rows or [self.row], self.modules,
                                              self.manifest,self.baseline,source_root)

    def two_root_inventory(self):
        mod = source.MARTINET_ENTRY
        self.manifest['roots'].append(mod)
        self.manifest['moduleRows'][mod] = {
            'owner': 'SawinTotallyRealTowers', 'path': 'Lean4/'+mod.replace('.', '/')+'.lean',
            'sha256': 'b'*64}
        self.summary.update(importRoots=list(self.manifest['roots']),
                            primaryModuleCount=2, loadedPrimaryModuleCount=2)
        self.summary['owners']['SawinTotallyRealTowers'].update(requestedModules=2, loadedModules=2)
        self.summary['allSelected']['declarations'] = 2
        self.modules.append({'module': mod, 'path': self.manifest['moduleRows'][mod]['path'],
                             'primaryOwner': 'SawinTotallyRealTowers', 'isLoaded': True})
        martinet = copy.deepcopy(self.row)
        martinet.update(name=source.MARTINET_MAIN, originModule=mod,
                        nameParts=[{'str': part} for part in source.MARTINET_MAIN.split('.')])
        return [self.row, martinet]

    def test_two_root_closure_requires_both_modules_loaded(self):
        rows = self.two_root_inventory()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = {
                source.ENTRY: 'theorem one : True := True.intro\n',
                source.MARTINET_ENTRY: 'import '+source.ENTRY+'\ntheorem two : True := one\n',
            }
            for module, text in sources.items():
                row = self.manifest['moduleRows'][module]
                path = root/row['path']; path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
                row.update(sha256=source.digest(path), imports=source.source_imports(text))
            closure = source.audit_rows(root, self.manifest)
            self.assertTrue(closure['exactClosure'])
            self.assertEqual(closure['moduleCount'], 2)
            self.assertEqual(self.check(rows)['safeDeclarations'], 2)
            self.modules[1]['isLoaded'] = False
            with self.assertRaisesRegex(ValueError, 'Module identity mismatch'):
                self.check(rows)

    def test_valid_inventory(self): self.assertEqual(self.check()['safeDeclarations'],1)
    def test_unsafe_rejected(self):
        self.row['isUnsafe']=True; self.row['isSafeKernelRoot']=False
        with self.assertRaisesRegex(ValueError,'Unsafe'): self.check()
    def test_new_partial_rejected(self):
        self.row['isPartial']=True; self.row['isSafeKernelRoot']=False
        with self.assertRaisesRegex(ValueError,'New partial'): self.check()
    def test_sorry_rejected(self):
        self.row['axioms'].append('sorryAx')
        with self.assertRaisesRegex(ValueError,'axiom/sorry'): self.check()
    def test_wrong_origin_rejected(self):
        self.row['originModule']='Other.Module'
        with self.assertRaisesRegex(ValueError,'origin'): self.check()
    def test_wrong_owner_count_rejected(self):
        self.summary['owners']['SawinTotallyRealTowers']['loadedModules']=0
        with self.assertRaisesRegex(ValueError,'Owner coverage'): self.check()
    def test_duplicate_declaration_rejected(self):
        with self.assertRaisesRegex(ValueError,'Duplicate'): self.check([self.row,self.row])
    def test_existing_partial_source_guard(self):
        partial=copy.deepcopy(self.row); partial.update(name='old._unsafe_rec',kind='definition',
                          isPartial=True,isSafeKernelRoot=False)
        old={k:partial[k] for k in ['name','nameParts','originModule','primaryOwner','isPartial','isUnsafe']}
        old.update(sourcePath=self.modules[0]['path'],currentSourceSHA256='b'*64,
                   historicalBodySHA256='c'*64)
        self.baseline['allowedPartialDeclarations']=[old]
        self.summary['allSelected']['declarations']=2
        with self.assertRaisesRegex(ValueError,'source changed'): self.check([self.row,partial])

    def test_all_seven_historical_partial_sources_match_body_and_current_hashes(self):
        root = Path(__file__).resolve().parents[1]
        baseline = json.loads((root/'.github/verification/historical-partial-baseline.json').read_text())
        manifest = json.loads((root/'.github/verification/source-manifest.json').read_text())
        self.assertEqual(len(baseline['allowedPartialDeclarations']), 7)
        for old in baseline['allowedPartialDeclarations']:
            with self.subTest(old=old['name']):
                path = old['sourcePath']
                self.assertEqual(manifest['moduleRows'][old['originModule']]['sha256'],
                                 old['currentSourceSHA256'])
                self.assertEqual(source.digest(root/path), old['currentSourceSHA256'])
                self.assertEqual(verify.historical_body_sha(root, path),
                                 old['historicalBodySHA256'])

    def test_historical_partial_header_must_be_exactly_recognized(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root/'Lean4/Proof.lean'; path.parent.mkdir()
            body = b'theorem old : True := True.intro\n'
            path.write_bytes(verify.COPYRIGHT_HEADER + body)
            self.assertEqual(verify.historical_body_sha(root, 'Lean4/Proof.lean'),
                             hashlib.sha256(body).hexdigest())
            path.write_bytes(b'/- other header -/\n\n' + body)
            with self.assertRaisesRegex(ValueError, 'recognized copyright header'):
                verify.historical_body_sha(root, 'Lean4/Proof.lean')

class ReplayTests(unittest.TestCase):
    def test_missing_completion_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)/'replay.log';p.write_text('REPLAY_START\n')
            with self.assertRaisesRegex(ValueError,'Missing'): verify.validate_replay(p,{'roots':[source.ENTRY]})
    def test_valid_completed_replay(self):
        inv={'phase':'inventory','roots':[source.ENTRY],'loaded_modules':[source.ENTRY,'Init'],
             'constant_count':12,'unsafe_skipped_count':1,'partial_skipped_count':2}
        done={'phase':'replay','result':'PASS','kernel':'official Lean 4.35.0-rc2'}
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)/'replay.log';p.write_text(json.dumps(inv)+'\n'+json.dumps(done)+'\n')
            result=verify.validate_replay(p,{'roots':[source.ENTRY],'moduleRows':{source.ENTRY:{}}})
            self.assertFalse(result['independentKernelCheckPerformed'])
            self.assertEqual(result['partialSkippedInImportedClosure'],2)

class WrapperPinTests(unittest.TestCase):
    def test_bundled_wrappers_match_pins_and_provenance(self):
        provenance = json.loads((SCRIPTS / 'wrapper-provenance.json').read_text())
        self.assertEqual(provenance['bundledPath'], '.github/verification')
        for name, expected in verify.WRAPPERS.items():
            self.assertEqual(source.digest(SCRIPTS / name), expected)
            self.assertEqual(provenance['bundledSHA256'][name], expected)

if __name__ == '__main__': unittest.main()
