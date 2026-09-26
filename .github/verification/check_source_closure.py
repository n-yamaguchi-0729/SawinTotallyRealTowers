#!/usr/bin/env python3
"""Check the SHA-pinned local import closure; this is not a proof checker."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import tomllib

ENTRY = 'SawinTotallyRealTowers.SawinTotallyRealTower'
MAIN = 'ClassFieldTower.Sawin.sawin_totally_real_tower'
MARTINET_ENTRY = 'SawinTotallyRealTowers.MartinetCorollary'
ALL_ENTRY = 'SawinTotallyRealTowers.All'
MARTINET_MAIN = 'ClassFieldTower.Sawin.exists_totallyReal_discr_le'
SHAFAREVICH_ENTRY = 'SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ShafarevichRelationRankBound'
SHAFAREVICH_MAIN = 'ClassFieldTower.Martinet.Shafarevich.shafarevich_relation_rank_bound'
ROOTS = [ALL_ENTRY, MARTINET_ENTRY]
REQUIRED_DECLARATIONS = [
    {'name': MAIN, 'originModule': ENTRY, 'kind': 'theorem'},
    {'name': MARTINET_MAIN, 'originModule': MARTINET_ENTRY, 'kind': 'theorem'},
    {'name': SHAFAREVICH_MAIN, 'originModule': SHAFAREVICH_ENTRY, 'kind': 'theorem'},
]
OWNERS = {'ClassFieldTheory': 690, 'GaloisCohomology': 154, 'ProCGroups': 321,
          'SawinTotallyRealTowers': 269, 'ValuedFieldTheory': 306}
MATHLIB = '065356127b1dc0016f66b7283ce0ce2c4055aa55'
TOOLCHAIN = 'leanprover/lean4:v4.35.0-rc2'
EXTERNAL = {'Mathlib', 'Lean', 'Init', 'Std', 'Batteries', 'Aesop', 'Qq', 'Plausible'}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def mask_comments_strings(source):
    result = []; i = 0; depth = 0; string = False
    while i < len(source):
        if depth:
            if source.startswith('/-', i): depth += 1; result.extend('  '); i += 2
            elif source.startswith('-/', i): depth -= 1; result.extend('  '); i += 2
            else: result.append('\n' if source[i] == '\n' else ' '); i += 1
        elif string:
            if source[i] == '\\' and i + 1 < len(source): result.extend('  '); i += 2
            elif source[i] == '"': string = False; result.append(' '); i += 1
            else: result.append('\n' if source[i] == '\n' else ' '); i += 1
        elif source.startswith('/-', i): depth = 1; result.extend('  '); i += 2
        elif source.startswith('--', i):
            end = source.find('\n', i)
            if end < 0: end = len(source)
            result.extend(' ' * (end - i)); i = end
        elif source[i] == '"': string = True; result.append(' '); i += 1
        else: result.append(source[i]); i += 1
    require(not depth and not string, 'Unclosed comment/string')
    return ''.join(result)

def source_imports(text):
    result = []; header = True
    for number, line in enumerate(mask_comments_strings(text).splitlines(), 1):
        line = line.strip()
        if not line: continue
        found = re.fullmatch(r'(?:(?:public|private|meta)\s+)*import\s+(.+)', line)
        if found:
            require(header, f'Import after module header at line {number}')
            body = found.group(1)
            if body.startswith('all '): body = body[4:]
            for module in body.split():
                require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", module),
                        f'Unsupported import spelling: {module}')
                result.append(module)
        elif line not in ('module', 'prelude'): header = False
    return result

def audit_rows(root, manifest):
    root = Path(root).resolve(); rows = manifest['moduleRows']; graph = {}
    require(rows and manifest['roots'], 'Empty manifest')
    for module, row in rows.items():
        require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", module), 'Invalid module name')
        expected = 'Lean4/' + module.replace('.', '/') + '.lean'
        require(row['path'] == expected and row['owner'] == module.split('.')[0],
                'Module path/owner mismatch: ' + module)
        path = root / expected
        require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(root),
                'Missing/unsafe source path: ' + expected)
        require(digest(path) == row['sha256'], 'Source SHA changed: ' + expected)
        text = path.read_text(); cleaned = mask_comments_strings(text)
        require(not re.search(r'\b(?:sorry|admit|native_decide)\b', cleaned),
                'Forbidden placeholder/compiler trust tactic: ' + module)
        require(not re.search(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|unsafe)\b',
                              cleaned, re.MULTILINE), 'Axiom/unsafe declaration: ' + module)
        imports = source_imports(text)
        require(sorted(imports) == sorted(row['imports']), 'Imports changed: ' + module)
        local = []
        for dep in imports:
            if dep in rows: local.append(dep)
            else: require(dep.split('.')[0] in EXTERNAL, 'Unresolved local import: ' + dep)
        graph[module] = local
    reached = set(); active = set()
    def visit(module):
        require(module in rows, 'Missing entry/local module: ' + module)
        require(module not in active, 'Import cycle: ' + module)
        if module in reached: return
        active.add(module)
        for dep in graph[module]: visit(dep)
        active.remove(module); reached.add(module)
    for entry in manifest['roots']: visit(entry)
    require(reached == set(rows), 'Manifest contains modules outside the entry closure')
    return {'moduleCount': len(rows), 'ownerCounts': dict(Counter(r['owner'] for r in rows.values())),
            'allModules': [], 'exactClosure': True, 'sourceSHA256Exact': True}

def audit(root, manifest):
    root = Path(root).resolve()
    require(manifest['roots'] == ROOTS and manifest['entryModule'] == ENTRY and
            manifest['entryDeclaration'] == MAIN and
            manifest['requiredDeclarations'] == [r['name'] for r in REQUIRED_DECLARATIONS],
            'Entrypoint policy changed')
    require(manifest['ownerCounts'] == OWNERS and
            manifest['moduleCount'] == len(manifest['moduleRows']) == sum(OWNERS.values()),
            'Frozen bundle owner/count policy changed')
    physical = {p.relative_to(root).as_posix() for p in (root / 'Lean4').rglob('*.lean')}
    expected = {r['path'] for r in manifest['moduleRows'].values()}
    require(physical == expected, 'Physical source set differs from the manifest')
    config = tomllib.loads((root / 'lakefile.toml').read_text())
    require(config['name'] == 'SawinTotallyRealTowers' and config['defaultTargets'] == ROOTS,
            'Lake package/default target changed')
    libs = {x['name']: x for x in config['lean_lib']}
    require(len(config['lean_lib']) == 5 and set(libs) == set(OWNERS), 'Library owners changed')
    for owner, lib in libs.items():
        require(lib.get('srcDir') == 'Lean4' and lib.get('roots') == [] and
                lib['globs'] == [owner + '.+'], 'Wrong library registration: ' + owner)
    require((root / 'lean-toolchain').read_text().strip() == TOOLCHAIN, 'Toolchain changed')
    require(len(config['require']) == 1 and config['require'][0]['name'] == 'mathlib' and
            config['require'][0]['rev'] == MATHLIB, 'Direct external dependency changed')
    lock = json.loads((root / 'lake-manifest.json').read_text())
    require(lock['name'] == config['name'], 'Lock package name mismatch')
    for pkg in lock['packages']:
        require(pkg['type'] == 'git' and re.fullmatch('[0-9a-f]{40}', pkg['rev']),
                'Unpinned dependency: ' + pkg['name'])
    require(next(p['rev'] for p in lock['packages'] if p['name'] == 'mathlib') == MATHLIB,
            'Mathlib lock revision changed')
    result = audit_rows(root, manifest)
    require(result['ownerCounts'] == OWNERS, 'Actual owner counts differ')
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--output', type=Path)
    parser.add_argument('--generated-manifest', type=Path)
    args = parser.parse_args()
    report = {'passed': False, 'proofCheckPerformed': False}
    try:
        manifest = json.loads((args.root / '.github/verification/source-manifest.json').read_text())
        report.update(audit(args.root, manifest), passed=True)
        if args.generated_manifest:
            generated = json.loads(args.generated_manifest.read_text())
            expected = {'roots': manifest['roots'], 'moduleRows': {
                name: {'owner': row['owner'], 'path': row['path']}
                for name, row in manifest['moduleRows'].items()}}
            require(generated == expected,
                    'Generated physical source manifest differs from SHA-pinned closure')
            report['generatedManifestConsistent'] = True
    except Exception as error: report['error'] = str(error)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))
    return 0 if report['passed'] else 1

if __name__ == '__main__':
    raise SystemExit(main())
