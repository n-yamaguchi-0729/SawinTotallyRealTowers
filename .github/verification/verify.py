#!/usr/bin/env python3
"""Serial source/build/API/inventory/export/NanoDa/official-kernel checks."""
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

from check_source_closure import (audit, digest, require, ENTRY, ROOTS, OWNERS, MATHLIB)

HERE = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ALLOWED_PARTS = {(('str', 'propext'),), (('str', 'Classical'), ('str', 'choice')),
                 (('str', 'Quot'), ('str', 'sound'))}
LEAN_REV = '293d5d0c0c3f3dded4688b3ccd6a33939ac5102b'
EXPORT_COMMIT = '076e8e57707e813375e8f9da8bf989799ace9680'
NANODA_COMMIT = '4c544ed4099c8227f07d5de77ad1e69fb0740a27'
WRAPPERS = {
    'Inventory.lean': 'e5f9906cebd8326517172b7e2bb0b9e288fe332763a1f4295b5ab3eeac93e075',
    'ExportSelected.lean': '214ca63daef63850b66520e0022b50d78c8020c1883edf91f95325662fd6aed0',
    'ReplaySix.lean': '262202e041f6af84d877960f6e037a1963e91ed8c1e93d4e5a7dbcdef5dd92e4',
}
COPYRIGHT_HEADER = (
    '/-\n'
    'Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.\n'
    'Released under Apache 2.0 license as described in the file LICENSE.\n'
    'Authors: Naganori Yamaguchi (assisted by OpenAI Codex)\n'
    '-/\n\n'
).encode()

def utc(): return datetime.now(timezone.utc).isoformat()
def save(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + '\n')

def unique_object(pairs):
    row = {}
    for key, value in pairs:
        require(key not in row, 'Duplicate JSON key: ' + key)
        row[key] = value
    return row

def name_parts(parts):
    require(isinstance(parts, list) and parts, 'Missing structural name')
    result = []
    for part in parts:
        require(isinstance(part, dict) and len(part) == 1, 'Invalid name component')
        kind, value = next(iter(part.items()))
        require((kind == 'str' and isinstance(value, str)) or
                (kind == 'num' and type(value) is int and value >= 0),
                'Invalid name component type')
        result.append((kind, value))
    return tuple(result)

def export_coverage(exported, inventory, selectors):
    """Check that the exporter retained the complete safe inventory by structural name."""
    names, declarations, axioms, metadata = {0: ()}, {}, set(), None
    lines = 0
    def declare(index, kind):
        name = names[index]
        require(name not in declarations, 'Duplicate exported declaration')
        declarations[name] = kind
        if kind == 'axiom': axioms.add(name)
    with exported.open() as stream:
        for lines, line in enumerate(stream, 1):
            obj = json.loads(line, object_pairs_hook=unique_object)
            if 'meta' in obj:
                require(metadata is None, 'Duplicate export metadata')
                metadata = obj['meta']
            if 'in' in obj:
                index = obj['in']
                require(index not in names, 'Duplicate export name index')
                require(('str' in obj) != ('num' in obj), 'Invalid export name record')
                part = obj['str'] if 'str' in obj else obj['num']
                suffix = name_parts([{'str': part['str']}] if 'str' in obj else [{'num': part['i']}])[0]
                names[index] = names[part['pre']] + (suffix,)
            for kind in ('axiom', 'def', 'opaque', 'thm', 'quot'):
                if kind in obj: declare(obj[kind]['name'], kind)
            if 'inductive' in obj:
                for kind in ('types', 'ctors', 'recs'):
                    for declaration in obj['inductive'][kind]:
                        declare(declaration['name'], kind)
    require(metadata is not None and lines > 0, 'Missing export metadata')
    selected = {name_parts(inventory[s]['nameParts']) for s in selectors}
    require(len(selected) == len(selectors), 'Selector spelling/structural collision')
    missing = sorted(s for s in selectors if name_parts(inventory[s]['nameParts']) not in declarations)
    return {'selectedDeclarationCount': len(selected), 'exportedDeclarationCount': len(declarations),
            'allSelectedPresent': not missing, 'missingSelectedDeclarations': missing,
            'axiomNameParts': sorted(axioms), 'unexpectedAxiomNameParts': sorted(axioms - ALLOWED_PARTS),
            'metadata': metadata, 'lines': lines}

def historical_body_sha(root, relative):
    root = Path(root).resolve()
    path = (root / relative).resolve()
    require(path.is_relative_to(root) and path.is_file(),
            'Historical partial source path escaped package')
    source = path.read_bytes()
    require(source.startswith(COPYRIGHT_HEADER),
            'Historical partial source does not have the recognized copyright header')
    return hashlib.sha256(source[len(COPYRIGHT_HEADER):]).hexdigest()

def validate_inventory_data(summary, declarations, modules, manifest, baseline, source_root):
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
            require(origin['path'] == old['sourcePath'] and
                    origin['sha256'] == old['currentSourceSHA256'],
                    'Historical partial current source changed: ' + name)
            require(historical_body_sha(source_root, origin['path']) == old['historicalBodySHA256'],
                    'Historical partial original source body changed: ' + name)
            partials[name] = row
        rows[name] = row
    require(rows and len(rows) == summary['allSelected']['declarations'], 'Declaration count mismatch')
    require(set(partials) == set(allowed_partial), 'Historical partial set mismatch')
    return {'declarations': len(rows), 'safeDeclarations': len(rows) - len(partials),
            'historicalPartialDeclarations': len(partials), 'unsafeDeclarations': 0,
            'ownerDeclarationCounts': dict(Counter(r['primaryOwner'] for r in rows.values())),
            'moduleCoverageExact': True, 'standardAxiomPolicyPassed': True,
            'partialExclusions': partials}

def validate_inventory(directory, manifest, baseline, source_root):
    result = validate_inventory_data(json.loads((directory / 'summary.json').read_text()),
        [json.loads(s) for s in (directory / 'declarations.jsonl').read_text().splitlines() if s],
        json.loads((directory / 'modules.json').read_text()), manifest, baseline, source_root)
    save(directory / 'explicit-partial-exclusions.json', result.pop('partialExclusions'))
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
    def __init__(self, root, output, exporter_checkout, nanoda_checkout, nanoda_binary):
        self.root = root.resolve(); self.output = output.resolve()
        self.exporter = exporter_checkout.resolve()
        self.nanoda_checkout = nanoda_checkout.resolve()
        self.nanoda = nanoda_binary.resolve()
        require(not self.output.is_relative_to(self.root), 'Output must be outside the checked package')
        self.output.mkdir(parents=True, exist_ok=False)
        self.env = dict(os.environ, LEAN_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
        self.env.pop('LEAN_PATH', None); self.env.pop('LEAN_SYSROOT', None)
        self.lake = shutil.which('lake')
        self.receipt = {'passed': False, 'startedUtc': utc(), 'stages': [],
            'entryModule': ENTRY, 'entryModules': ROOTS, 'nanoDaRun': False, 'independentKernelCheckPerformed': False}
        self.sealed = {}
        self.started = time.monotonic()

    def checkpoint(self): save(self.output / 'receipt.json', self.receipt)

    def seal(self, *paths):
        for path in paths:
            path = Path(path).resolve()
            require(path.is_file(), 'Missing verification artifact: ' + str(path))
            self.sealed[str(path)] = digest(path)

    def stage(self, name, command, capture=False, env=None, output=None, validate=None):
        command = [str(x) for x in command]
        row = {'name': name, 'command': command, 'startedUtc': utc(), 'passed': False}
        self.receipt['stages'].append(row); self.checkpoint()
        started = time.monotonic(); log = self.output / (name + '.log')
        with log.open('wb') as stream:
            if output is None:
                proc = subprocess.run(command, cwd=self.root, env=env or self.env,
                                      stdout=stream, stderr=subprocess.STDOUT)
            else:
                with output.open('wb') as exported:
                    proc = subprocess.run(command, cwd=self.root, env=env or self.env,
                                          stdout=exported, stderr=stream)
        row.update(exitCode=proc.returncode, elapsedSeconds=round(time.monotonic()-started, 3),
                   log=str(log), logSHA256=digest(log), completedUtc=utc())
        if output is not None:
            row.update(output=str(output), outputSHA256=digest(output))
        self.checkpoint(); require(proc.returncode == 0, name + ' failed; see ' + str(log))
        if validate is not None:
            row['validation'] = validate(log)
        self.seal(log)
        if output is not None: self.seal(output)
        row['passed'] = True
        self.checkpoint()
        return log.read_text().strip() if capture else (output or log)

    def audit_stage(self, name, validate):
        row = {'name': name, 'command': None, 'startedUtc': utc(), 'passed': False}
        self.receipt['stages'].append(row); self.checkpoint()
        started = time.monotonic()
        try:
            row['validation'] = validate()
            row['passed'] = True
            row['exitCode'] = 0
            return row['validation']
        except BaseException as error:
            row.update(exitCode=1, error=str(error))
            raise
        finally:
            row.update(elapsedSeconds=round(time.monotonic()-started, 3), completedUtc=utc())
            self.checkpoint()

    def git(self, path, *args):
        return subprocess.check_output(['git', '-C', str(path), *args], cwd=self.root,
            env=self.env, text=True, stderr=subprocess.STDOUT).strip()

    def checker_tool_identity(self):
        result = {}
        for name, path, commit in [('lean4export', self.exporter, EXPORT_COMMIT),
                                   ('nanoda_lib', self.nanoda_checkout, NANODA_COMMIT)]:
            require(path.is_dir() and Path(self.git(path, 'rev-parse', '--show-toplevel')).resolve() == path,
                    'Checker tool path is not its checkout root: ' + name)
            head = self.git(path, 'rev-parse', 'HEAD')
            require(head == commit and not self.git(path, 'status', '--porcelain',
                                                   '--untracked-files=all'),
                    'Checker tool checkout is not exact and clean: ' + name)
            result[name] = {'path': str(path), 'revision': head}
        require(self.nanoda.is_file() and os.access(self.nanoda, os.X_OK) and
                self.nanoda.is_relative_to(self.nanoda_checkout),
                'Missing executable NanoDa binary in pinned checkout')
        return result

    def checker_tool_paths(self):
        core = self.exporter / '.lake/build/lib/lean'
        require((core / 'Export.olean').is_file(), 'Pinned exporter Export module was not built')
        paths = {self.nanoda, self.exporter / 'Export.lean', self.exporter / 'lean-toolchain'}
        paths.update(core.rglob('*.olean*'))
        require(all(p.is_file() for p in paths), 'Missing pinned checker tool input')
        return paths

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
        for folder in ['Lean4','tests','.github']:
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

    def guard(self, project, runtime, ident, tools):
        require(self.git(self.root, 'rev-parse', 'HEAD') == self.receipt['gitCommit'] and
                not self.git(self.root, 'status', '--porcelain', '--untracked-files=all'),
                'Package commit/working tree changed')
        require(self.snapshots(self.project_paths()) == project, 'Package input changed')
        require(self.dependencies() == ident['dependencies'], 'Dependency identity changed')
        require(self.snapshots(self.runtime_paths(ident)) == runtime, 'Compiled/toolchain input changed')
        require(self.checker_tool_identity() == ident['checkerTools'], 'Checker tool revision changed')
        require(self.snapshots(self.checker_tool_paths()) == tools,
                'Checker tool source/binary input changed')
        require(all(Path(path).is_file() and digest(path) == sha
                    for path, sha in self.sealed.items()),
                'A completed verification artifact changed')

    def select_safe_roots(self, inventory_dir):
        summary = json.loads((inventory_dir / 'summary.json').read_text())
        rows = {}
        for line in (inventory_dir / 'declarations.jsonl').read_text().splitlines():
            if not line: continue
            row = json.loads(line, object_pairs_hook=unique_object)
            require(row['name'] not in rows, 'Duplicate safe-root inventory name')
            rows[row['name']] = row
        selectors = sorted(name for name, row in rows.items() if row['isSafeKernelRoot'])
        require(selectors and len(selectors) == summary['allSelected']['safeDeclarations'],
                'Safe-root selector count mismatch')
        recorded = (inventory_dir / 'selectors/all-selected.safe.txt').read_text().splitlines()
        require(len(recorded) == len(set(recorded)) and set(recorded) == set(selectors),
                'Inventory safe-root selector artifact differs from declaration inventory')
        counts = Counter(rows[name]['primaryOwner'] for name in selectors)
        for owner, owner_summary in summary['owners'].items():
            require(counts[owner] == owner_summary['statistics']['safeDeclarations'],
                    'Safe-root owner count mismatch: ' + owner)
        self.inventory_rows = rows; self.selectors = selectors
        self.selector_path = self.output / 'safe-union.txt'
        self.selector_path.write_text('\n'.join(selectors) + '\n')
        result = {'safeRootCount': len(selectors), 'ownerCounts': dict(counts),
                  'excludedUnsafe': sum(row['isUnsafe'] for row in rows.values()),
                  'excludedPartial': sum(row['isPartial'] for row in rows.values())}
        save(self.output / 'selection.json', result)
        self.seal(self.selector_path, self.output / 'selection.json')
        return result

    def check_export(self, exported):
        result = export_coverage(exported, self.inventory_rows, self.selectors)
        save(self.output / 'coverage-report.json', result)
        require(result['allSelectedPresent'] and not result['unexpectedAxiomNameParts'],
                'Export omitted a safe root or introduced an unpermitted axiom')
        lean = result['metadata']['lean']
        require(lean['version'] == '4.34.0' and lean['githash'] == LEAN_REV,
                'Exporter Lean identity mismatch')
        self.seal(self.output / 'coverage-report.json')
        return {'completeSafeUnion': True, 'selectedRootCount': len(self.selectors),
                'exportedDeclarationCount': result['exportedDeclarationCount']}

    def check_nanoda(self, log):
        output = log.read_text()
        counts = re.findall(r'^Checked ([0-9]+) declarations with no errors\.?$', output, re.MULTILINE)
        require(len(counts) == 1 and int(counts[0]) >= len(self.selectors),
                'Missing exact NanoDa completion')
        require('skipping' not in output.lower(), 'NanoDa skipped declarations')
        return {'checkedDeclarationsIncludingDependencies': int(counts[0]),
                'strictThreeAxioms': True}

    def run(self):
        try:
            require(self.lake, 'lake is not on PATH')
            self.receipt['gitCommit'] = self.git(self.root, 'rev-parse', 'HEAD')
            require(not self.git(self.root, 'status', '--porcelain', '--untracked-files=all'),
                    'Verification requires a clean committed checkout')
            manifest = json.loads((self.root/'.github/verification/source-manifest.json').read_text())
            baseline = json.loads((self.root/'.github/verification/historical-partial-baseline.json').read_text())
            require(len(baseline['allowedPartialDeclarations']) == 7, 'Expected seven historical partials')
            for name, expected in WRAPPERS.items():
                require(digest(HERE/name) == expected, 'Official wrapper modified: ' + name)
            self.receipt['sourceAudit'] = audit(self.root, manifest)
            project = self.snapshots(self.project_paths())
            self.stage('python-tests', [sys.executable,'-B','-m','unittest','discover','-s','tests',
                                       '-p','test_*.py','-v'])
            self.stage('build', [self.lake,'--no-ansi','--rehash','--wfail','build', *ROOTS])
            self.stage('statement', [self.lake,'env','lean','-j1','--error=warning','tests/Statement.lean'])
            self.stage('martinet-statement', [self.lake,'env','lean','-j1','--error=warning',
                                              'tests/MartinetStatement.lean'])
            require(self.snapshots(self.project_paths()) == project, 'Input changed during build')
            version = self.stage('lean-version', [self.lake,'env','lean','--version'], True)
            require('version 4.34.0' in version and LEAN_REV in version, 'Lean identity mismatch')
            prefix = self.stage('lean-prefix', [self.lake,'env','lean','--print-prefix'], True)
            search = self.stage('lean-search-path', [self.lake,'env','printenv','LEAN_PATH'], True)
            ident = {'version': version, 'prefix': prefix, 'searchPath': search,
                     'dependencies': self.dependencies(),
                     'checkerTools': self.checker_tool_identity()}
            self.receipt['identity'] = ident
            runtime = self.snapshots(self.runtime_paths(ident))
            tools = self.snapshots(self.checker_tool_paths())
            save(self.output/'sealed-inputs.json', {'project': project, 'runtime': runtime,
                 'checkerTools': tools, 'identity': ident,
                 'gitCommit': self.receipt['gitCommit']})
            self.receipt['sealedInputsSHA256'] = digest(self.output/'sealed-inputs.json')
            self.seal(self.output/'sealed-inputs.json')
            self.guard(project, runtime, ident, tools)
            inv = self.output/'inventory'; inv.mkdir()
            command = [self.lake,'env',str(Path(prefix)/'bin/lean'),'-j1','--run',str(HERE/'Inventory.lean')]
            self.stage('inventory', command + [str(self.root/'.github/verification/source-manifest.json'), str(inv)])
            self.receipt['inventory'] = validate_inventory(inv, manifest, baseline, self.root)
            for path in inv.rglob('*'):
                if path.is_file(): self.seal(path)
            self.guard(project, runtime, ident, tools)
            self.receipt['selection'] = self.audit_stage('selection', lambda: self.select_safe_roots(inv))
            self.guard(project, runtime, ident, tools)
            export_env = dict(self.env, LEAN_PATH=search + os.pathsep +
                              str(self.exporter/'.lake/build/lib/lean'))
            exported = self.stage('export', [str(Path(prefix)/'bin/lean'), '-j1', '--run',
                str(HERE/'ExportSelected.lean'), str(self.selector_path), *manifest['roots']],
                env=export_env, output=self.output/'selected.ndjson')
            self.guard(project, runtime, ident, tools)
            self.receipt['coverage'] = self.audit_stage('coverage', lambda: self.check_export(exported))
            self.guard(project, runtime, ident, tools)
            config = {'export_file_path': str(exported), 'use_stdin': False,
                'permitted_axioms': sorted(ALLOWED), 'unpermitted_axiom_hard_error': True,
                'unsafe_permit_all_axioms': False, 'num_threads': 1,
                'nat_extension': True, 'string_extension': True, 'pp_declars': [],
                'unknown_pp_declar_hard_error': True, 'print_success_message': True,
                'print_axioms': True, 'pp_to_stdout': True}
            config_path = self.output/'nanoda-config.json'; save(config_path, config)
            self.seal(config_path)
            self.stage('nanoda', [self.nanoda, config_path], validate=self.check_nanoda)
            self.receipt['nanoda'] = self.receipt['stages'][-1]['validation']
            self.receipt['nanoDaRun'] = True
            self.receipt['independentKernelCheckPerformed'] = True
            self.guard(project, runtime, ident, tools)
            self.stage('replay', [self.lake,'env',str(Path(prefix)/'bin/lean'),'-j1','--run',
                                 str(HERE/'ReplaySix.lean'), *manifest['roots']])
            self.receipt['replay'] = validate_replay(self.output/'replay.log', manifest)
            self.guard(project, runtime, ident, tools)
            core = {'build', 'inventory', 'selection', 'export', 'coverage', 'nanoda', 'replay'}
            require([row['name'] for row in self.receipt['stages'] if row['name'] in core] ==
                    ['build', 'inventory', 'selection', 'export', 'coverage', 'nanoda', 'replay'] and
                    all(row['passed'] for row in self.receipt['stages']),
                    'Mandatory verification stage missing or failed')
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
    parser.add_argument('--exporter-checkout', type=Path, required=True)
    parser.add_argument('--nanoda-checkout', type=Path, required=True)
    parser.add_argument('--nanoda-binary', type=Path, required=True)
    args = parser.parse_args()
    try: return Runner(args.package_root, args.output, args.exporter_checkout,
                       args.nanoda_checkout, args.nanoda_binary).run()
    except Exception as error:
        print('Verification setup failed: ' + str(error), file=sys.stderr)
        return 2

if __name__ == '__main__': raise SystemExit(main())
