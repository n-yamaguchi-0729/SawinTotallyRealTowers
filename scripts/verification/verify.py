#!/usr/bin/env python3
"""Serial source/build/API/all-declaration audit/official-kernel checks. No NanoDa."""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from check_source_closure import (audit, digest, require, ENTRY, ROOTS,
                                  REQUIRED_DECLARATIONS, OWNERS, MATHLIB)

HERE = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LEAN_REV = '293d5d0c0c3f3dded4688b3ccd6a33939ac5102b'
WRAPPERS = {
    'Inventory.lean': 'd6714ed33fa2acdffeaf71c74a3f7f43b8aa1eb1148d2a48c19aa84f91a51b10',
    'ReplaySix.lean': 'f3a80238936e070af86c4559623cddfac04c7d4acc8dd09d294776eec4a49ee4',
}

def utc(): return datetime.now(timezone.utc).isoformat()
def save(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + '\n')

def validate_inventory_data(summary, declarations, modules, manifest, baseline, required):
    expected = manifest['moduleRows']; roots = manifest['roots']
    allowed_partial = {r['name']: r for r in baseline['allowedPartialDeclarations']}
    require(len(allowed_partial) == len(baseline['allowedPartialDeclarations']), 'Duplicate baseline name')
    require(summary['auditPassed'] and summary['moduleCoverageExact'], 'Inventory audit failed')
    require(summary['importRoots'] == roots and summary['importLevel'] == 'private' and
            summary['importTrustLevel'] == 0, 'Wrong inventory root/import mode')
    require(summary['primaryModuleCount'] == summary['loadedPrimaryModuleCount'] == len(expected),
            'Inventory module count mismatch')
    require(not summary['missingRequestedModules'] and not summary['missingRootModules'],
            'Requested module omitted')
    require(summary['repairedModuleCount'] == 0, 'Unexpected repaired/extra selection')
    require(set(summary['allowedAxioms']) == ALLOWED, 'Axiom policy mismatch')
    module_rows = {r['module']: r for r in modules}
    require(len(module_rows) == len(modules) and set(module_rows) == set(expected),
            'Module inventory set mismatch')
    for name, row in module_rows.items():
        require(row['isLoaded'] and row['primaryOwner'] == expected[name]['owner'] and
                row['path'] == expected[name]['path'], 'Module identity mismatch: ' + name)
    counts = Counter(row['owner'] for row in expected.values())
    require(set(summary['owners']) == set(counts), 'Owner inventory set mismatch')
    for owner, count in counts.items():
        row = summary['owners'][owner]
        require(row['requestedModules'] == row['loadedModules'] == count and row['moduleCoverageExact'],
                'Owner coverage mismatch: ' + owner)
    rows = {}; partials = {}
    for row in declarations:
        name = row['name']; require(name not in rows, 'Duplicate declaration: ' + name)
        origin = expected.get(row['originModule'])
        require(origin is not None and row['primaryOwner'] == origin['owner'] and row['isPrimary'],
                'Declaration origin/owner mismatch: ' + name)
        require(row['nameToStringRoundTrip'] and not row['nonstandardAxioms'] and
                set(row['axioms']) <= ALLOWED and not row['hasTransitiveSorry'] and
                not row['typeHasSorry'] and not row['valueHasSorry'] and
                not row['hasSyntheticSorry'] and not row['hasNonSyntheticSorry'],
                'Nonstandard axiom/sorry/name found: ' + name)
        require(not row['isUnsafe'], 'Unsafe declaration: ' + name)
        require(row['isSafeKernelRoot'] == (not row['isUnsafe'] and not row['isPartial']),
                'Inconsistent safe classification: ' + name)
        if row['isPartial']:
            old = allowed_partial.get(name)
            require(old is not None, 'New partial declaration: ' + name)
            require(all(row[k] == old[k] for k in
                        ['nameParts', 'originModule', 'primaryOwner', 'isPartial', 'isUnsafe']),
                    'Historical partial identity changed: ' + name)
            require(origin['path'] == old['sourcePath'] and origin['sha256'] == old['sourceSHA256'],
                    'Historical partial source changed: ' + name)
            partials[name] = row
        rows[name] = row
    require(rows and len(rows) == summary['allSelected']['declarations'], 'Declaration count mismatch')
    require(set(partials) == set(allowed_partial), 'Historical partial set mismatch')
    for item in required['declarations']:
        row = rows.get(item['name'])
        require(row is not None and row['isSafeKernelRoot'] and row['kind'] == item['kind'] and
                row['originModule'] == item['originModule'], 'Required mathematical theorem absent/unsafe')
    return {'declarations': len(rows), 'safeDeclarations': len(rows) - len(partials),
            'historicalPartialDeclarations': len(partials), 'unsafeDeclarations': 0,
            'ownerDeclarationCounts': dict(Counter(r['primaryOwner'] for r in rows.values())),
            'moduleCoverageExact': True, 'standardAxiomPolicyPassed': True,
            'partialExclusions': partials,
            'requiredDeclarations': {r['name']: rows[r['name']] for r in required['declarations']}}

def validate_inventory(directory, manifest, baseline, required):
    result = validate_inventory_data(json.loads((directory / 'summary.json').read_text()),
        [json.loads(s) for s in (directory / 'declarations.jsonl').read_text().splitlines() if s],
        json.loads((directory / 'modules.json').read_text()), manifest, baseline, required)
    save(directory / 'explicit-partial-exclusions.json', result.pop('partialExclusions'))
    save(directory / 'required-declarations.json', result.pop('requiredDeclarations'))
    return result

def validate_replay(path, manifest):
    records = [json.loads(line) for line in path.read_text().splitlines() if line.startswith('{')]
    inventories = [r for r in records if r.get('phase') == 'inventory']
    results = [r for r in records if r.get('phase') == 'replay']
    require(len(inventories) == len(results) == 1, 'Missing/duplicate replay records')
    inv = inventories[0]; result = results[0]
    require(result['result'] == 'PASS' and result['kernel'] == 'official Lean 4.34.0',
            'Official replay did not pass')
    require(inv['roots'] == manifest['roots'], 'Replay root mismatch')
    loaded = inv['loaded_modules']
    require(len(loaded) == len(set(loaded)), 'Duplicate loaded module')
    local = {m for m in loaded if m.split('.')[0] in OWNERS}
    require(local == set(manifest['moduleRows']), 'Replay local module closure mismatch')
    return {'officialKernelReplay': 'PASS', 'loadedModuleCount': len(loaded),
            'loadedConstantCount': inv['constant_count'], 'localModuleCoverageExact': True,
            'unsafeSkippedInImportedClosure': inv['unsafe_skipped_count'],
            'partialSkippedInImportedClosure': inv['partial_skipped_count'],
            'axiomPolicyEnforcedBySeparateInventory': True,
            'independentKernelCheckPerformed': False}

class Runner:
    def __init__(self, root, output):
        self.root = root.resolve(); self.output = output.resolve()
        require(not self.output.is_relative_to(self.root), 'Output must be outside the checked package')
        self.output.mkdir(parents=True, exist_ok=False)
        self.env = dict(os.environ, LEAN_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
        self.env.pop('LEAN_PATH', None); self.env.pop('LEAN_SYSROOT', None)
        self.lake = shutil.which('lake')
        self.receipt = {'passed': False, 'startedUtc': utc(), 'stages': [],
            'entryModule': ENTRY, 'entryModules': ROOTS, 'nanoDaRun': False, 'independentKernelCheckPerformed': False}
        self.started = time.monotonic()

    def checkpoint(self): save(self.output / 'receipt.json', self.receipt)

    def stage(self, name, command, capture=False):
        command = [str(x) for x in command]
        row = {'name': name, 'command': command, 'startedUtc': utc()}
        self.receipt['stages'].append(row); self.checkpoint()
        started = time.monotonic(); log = self.output / (name + '.log')
        with log.open('wb') as stream:
            proc = subprocess.run(command, cwd=self.root, env=self.env,
                                  stdout=stream, stderr=subprocess.STDOUT)
        row.update(exitCode=proc.returncode, elapsedSeconds=round(time.monotonic()-started, 3),
                   log=str(log), logSHA256=digest(log), completedUtc=utc())
        self.checkpoint(); require(proc.returncode == 0, name + ' failed; see ' + str(log))
        return log.read_text().strip() if capture else log

    def git(self, path, *args):
        return subprocess.check_output(['git', '-C', str(path), *args], cwd=self.root,
            env=self.env, text=True, stderr=subprocess.STDOUT).strip()

    def dependencies(self):
        lock = json.loads((self.root/'lake-manifest.json').read_text()); result = {}
        require(lock['packagesDir'] == '.lake/packages', 'Unexpected package directory')
        for pkg in lock['packages']:
            require(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', pkg['name']), 'Invalid package name')
            path = self.root/lock['packagesDir']/pkg['name']
            require(path.resolve().is_relative_to(self.root), 'Dependency escapes standalone package')
            head = self.git(path, 'rev-parse', 'HEAD')
            require(head == pkg['rev'] and not self.git(path, 'status', '--porcelain',
                                                      '--untracked-files=all'),
                    'Dependency is not the exact clean revision: ' + pkg['name'])
            result[pkg['name']] = {'path': str(path), 'revision': head}
        require(result['mathlib']['revision'] == MATHLIB, 'Mathlib revision changed')
        return result

    def project_paths(self):
        paths = {self.root / n for n in ['lakefile.toml','lake-manifest.json','lean-toolchain',
                                         'LICENSE','README.md','.gitignore']}
        for folder in ['Lean4','scripts','tests','verification','.github']:
            paths.update(p for p in (self.root/folder).rglob('*') if p.is_file()
                         and '__pycache__' not in p.parts)
        return paths

    def snapshots(self, paths):
        return {str(p): digest(p) for p in sorted(paths)}

    def runtime_paths(self, ident):
        paths = {Path(ident['prefix'])/'bin/lean',
                 Path(ident['prefix'])/'src/lean/Lean/Replay.lean'}
        directories = {Path(ident['prefix'])/'lib'}
        toolchain_lean = (Path(ident['prefix'])/'lib'/'lean').resolve()
        for item in ident['searchPath'].split(os.pathsep):
            if item:
                path = Path(item)
                if not path.is_absolute(): path = self.root/path
                path = path.resolve()
                require(path.is_relative_to(self.root/'.lake') or path == toolchain_lean,
                        'Unexpected external LEAN_PATH')
                directories.add(path)
        for directory in directories:
            if directory.is_dir():
                paths.update(p for p in directory.rglob('*') if p.is_file() and
                    ('.olean' in p.name or p.suffix in {'.so','.dll','.dylib'}))
        for dep in ident['dependencies'].values():
            base = Path(dep['path'])
            for name in self.git(base, 'ls-files').splitlines():
                p = base/name
                if p.is_file() and (p.suffix in {'.lean','.toml','.json'} or p.name=='lean-toolchain'):
                    paths.add(p)
        return paths

    def guard(self, project, runtime, ident):
        require(self.git(self.root, 'rev-parse', 'HEAD') == self.receipt['gitCommit'] and
                not self.git(self.root, 'status', '--porcelain', '--untracked-files=all'),
                'Package commit/working tree changed')
        require(self.snapshots(self.project_paths()) == project, 'Package input changed')
        require(self.dependencies() == ident['dependencies'], 'Dependency identity changed')
        require(self.snapshots(self.runtime_paths(ident)) == runtime, 'Compiled/toolchain input changed')

    def run(self):
        try:
            require(self.lake, 'lake is not on PATH')
            self.receipt['gitCommit'] = self.git(self.root, 'rev-parse', 'HEAD')
            require(not self.git(self.root, 'status', '--porcelain', '--untracked-files=all'),
                    'Verification requires a clean committed checkout')
            manifest = json.loads((self.root/'verification/source-manifest.json').read_text())
            baseline = json.loads((self.root/'verification/historical-partial-baseline.json').read_text())
            required = json.loads((self.root/'verification/required-declarations.json').read_text())
            require(len(baseline['allowedPartialDeclarations']) == 7, 'Expected seven historical partials')
            require(required['declarations'] == REQUIRED_DECLARATIONS,
                    'Required endpoint contract changed')
            for name, expected in WRAPPERS.items():
                require(digest(HERE/name) == expected, 'Official wrapper modified: ' + name)
            self.receipt['sourceAudit'] = audit(self.root, manifest)
            project = self.snapshots(self.project_paths())
            self.stage('python-tests', [sys.executable,'-B','-m','unittest','discover','-s','tests',
                                       '-p','test_*.py','-v'])
            self.stage('build', [self.lake,'--wfail','build'])
            self.stage('statement', [self.lake,'env','lean','-j1','--error=warning','tests/Statement.lean'])
            self.stage('martinet-statement', [self.lake,'env','lean','-j1','--error=warning',
                                              'tests/MartinetStatement.lean'])
            require(self.snapshots(self.project_paths()) == project, 'Input changed during build')
            version = self.stage('lean-version', [self.lake,'env','lean','--version'], True)
            require('version 4.34.0' in version and LEAN_REV in version, 'Lean identity mismatch')
            prefix = self.stage('lean-prefix', [self.lake,'env','lean','--print-prefix'], True)
            search = self.stage('lean-search-path', [self.lake,'env','printenv','LEAN_PATH'], True)
            ident = {'version': version, 'prefix': prefix, 'searchPath': search,
                     'dependencies': self.dependencies()}
            self.receipt['identity'] = ident
            runtime = self.snapshots(self.runtime_paths(ident))
            save(self.output/'sealed-inputs.json', {'project': project, 'runtime': runtime,
                 'identity': ident, 'gitCommit': self.receipt['gitCommit']})
            self.receipt['sealedInputsSHA256'] = digest(self.output/'sealed-inputs.json')
            self.guard(project, runtime, ident)
            inv = self.output/'inventory'; inv.mkdir()
            command = [self.lake,'env',str(Path(prefix)/'bin/lean'),'-j1','--run',str(HERE/'Inventory.lean')]
            self.stage('inventory', command + [str(self.root/'verification/source-manifest.json'), str(inv)])
            self.receipt['inventory'] = validate_inventory(inv, manifest, baseline, required)
            self.guard(project, runtime, ident)
            self.stage('replay', [self.lake,'env',str(Path(prefix)/'bin/lean'),'-j1','--run',
                                 str(HERE/'ReplaySix.lean'), *manifest['roots']])
            self.receipt['replay'] = validate_replay(self.output/'replay.log', manifest)
            self.guard(project, runtime, ident)
            self.receipt.update(passed=True, inputsUnchanged=True)
        except BaseException as error:
            self.receipt['error'] = str(error)
        finally:
            self.receipt.update(completedUtc=utc(), elapsedSeconds=round(time.monotonic()-self.started,3))
            self.receipt['artifactsSHA256'] = {str(p.relative_to(self.output)): digest(p)
                for p in sorted(self.output.rglob('*')) if p.is_file() and p.name != 'receipt.json'}
            self.checkpoint()
        print(json.dumps(self.receipt, ensure_ascii=False))
        return 0 if self.receipt['passed'] else 1

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package-root', type=Path, default=HERE.parents[1])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    try: return Runner(args.package_root, args.output).run()
    except Exception as error:
        print('Verification setup failed: ' + str(error), file=sys.stderr)
        return 2

if __name__ == '__main__': raise SystemExit(main())
