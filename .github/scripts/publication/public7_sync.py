#!/usr/bin/env python3
"""Plan/apply minimal canonical extracts, CI and their actual source notices.

This module never builds Lean, commits, pushes or calls write APIs.

Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0. Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The nested-comment-aware parser is moved unchanged from the existing NYLL
publication exporter; this is its portable owner for future public syncs.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile
import tomllib

from public_ci import desired_ci
from public_extract_provenance import (provenance_files, managed_provenance_paths,
    readme_for_extract, sawin_verification_readme, local_markdown_links)
from public_sawin import desired_sawin
from ci_templates.generate_manifest import header_imports

# Runtime paths are supplied explicitly; this module does not depend on a
# developer checkout, work/tmp, or another unpublished helper.
ROOT = Path()
CLONES = Path()
SOURCE = ''
TOPICS = [
    ['ProCGroups', 'ValuedFieldTheory', 'GaloisCohomology', 'SchemeTheory'],
    ['ClassFieldTheory', 'AlgebraicCurves', 'EtaleFundamentalGroups', 'EtaleCohomology',
     'AbelianVarieties'],
    ['SawinTotallyRealTowers', 'JacobianVarieties', 'Yamaguchi26AbfaithfulGalois',
     'Yamaguchi26SolvableCoverings', 'AnabelianGeometry'],
]
DEPTH = {topic: depth for depth, topics in enumerate(TOPICS, 1) for topic in topics}


PRIMARY = {
    'ProCGroups': ['ProCGroups'],
    'ClassFieldTheory': ['ClassFieldTheory'],
    'SawinTotallyRealTowers': ['SawinTotallyRealTowers'],
    'EtaleFundamentalGroupsAndCohomology': ['EtaleFundamentalGroups', 'EtaleCohomology'],
    'JacobianVarieties': ['JacobianVarieties'],
    'YamaguchiPapersFormalization': ['Yamaguchi26AbfaithfulGalois',
        'Yamaguchi26SolvableCoverings'],
    'AnabelianGeometry': ['AnabelianGeometry'],
}

def mask_comments_and_strings(text: str) -> str:
    """Retain offsets/newlines while masking nested comments and string contents."""
    masked = list(text)
    i = 0
    depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                masked[i:i+2] = '  '
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                masked[i:i+2] = '  '
                depth -= 1
                i += 2
            else:
                if text[i] != '\n':
                    masked[i] = ' '
                i += 1
        elif quoted:
            if text[i] == '\\' and i + 1 < len(text):
                masked[i:i+2] = '  '
                i += 2
            else:
                if text[i] == '"':
                    quoted = False
                if text[i] != '\n':
                    masked[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            masked[i:i+2] = '  '
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            masked[i:end] = ' ' * (end - i)
            i = end
        elif text[i] == '"':
            masked[i] = ' '
            quoted = True
            i += 1
        else:
            i += 1
    if depth or quoted:
        raise ValueError('Unclosed source comment or string')
    return ''.join(masked)


def imports(text: str) -> list[tuple[str, int, int]]:
    return header_imports(text)


def require(condition, message):
    if not condition:
        raise ValueError(message)

def git(root, *args):
    return subprocess.check_output(['git', *args], cwd=root)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def module(path):
    return path[:-5].replace('/', '.')

def safe_path(root, rel):
    p = Path(rel)
    require(not p.is_absolute() and '..' not in p.parts, 'Unsafe relative path: ' + rel)
    full = root / p
    require(full.resolve().is_relative_to(root.resolve()), 'Escaped path: ' + rel)
    require(not any(q.is_symlink() for q in [full, *full.parents] if q != root.parent),
            'Symlink path: ' + str(full))
    return full

def require_source_clean(repo):
    require(not git(repo, 'status', '--porcelain', '-z'),
            'Public checkout contains uncommitted changes: ' + repo.name)


def canonical():
    require(re.fullmatch('[0-9a-f]{40}', SOURCE), 'Source is not immutable SHA')
    data = git(ROOT, 'archive', '--format=tar', SOURCE, 'Nyll', 'Nyll.lean',
        'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'LICENSE',
        '.github/scripts/publication')
    with tarfile.open(fileobj=io.BytesIO(data)) as archive:
        files = {}
        for entry in archive:
            if entry.isdir():
                continue
            require(entry.isfile(), 'Nonregular source: ' + entry.name)
            files[entry.name] = archive.extractfile(entry).read()
    cfg = tomllib.loads(files['lakefile.toml'].decode())
    order = [s.split('.')[1] for s in cfg['lean_lib'][0]['globs'] if s.endswith('.+')]
    require(set(order) == set(DEPTH), 'Canonical library order/depth map differs')
    # The distributed publication package also contains Lean checker programs.
    # Only the mathematical library belongs to the import/closure graph.
    lean = {module(p): data for p, data in files.items()
            if p.endswith('.lean') and (p == 'Nyll.lean' or p.startswith('Nyll/'))}
    source_imports = {m: [n for n, _, _ in imports(b.decode())] for m, b in lean.items()}
    graph = {m: [d for d in ds if d == 'Nyll' or d.startswith('Nyll.')] for m, ds in source_imports.items()}
    for m, ds in graph.items():
        for d in ds:
            require(d in graph, 'Missing local import: ' + m + ' -> ' + d)
            if m not in ('Nyll', 'Nyll.All'):
                require(d not in ('Nyll', 'Nyll.All'), 'Root import from leaf: ' + m)
                require(DEPTH[m.split('.')[1]] >= DEPTH[d.split('.')[1]], 'Reverse import: ' + m)
    visited, active = set(), set()
    def visit(m):
        require(m not in active, 'Cycle: ' + m)
        if m in visited:
            return
        active.add(m)
        for d in graph[m]:
            visit(d)
        active.remove(m)
        visited.add(m)
    visit('Nyll')
    require(visited == set(graph), 'Canonical source is not all reachable')
    return files, cfg, order, graph, source_imports

def desired_extract(files, cfg, order, graph, source_imports, primary):
    # Primary library aggregates retain all target-library source. Dependencies
    # are selected by actual module imports, never by the dependency's family.
    primary_roots = ['Nyll.' + f + '.All' for f in order if f in primary]
    require(len(primary_roots) == len(primary), 'Unknown or duplicate primary library')
    selected = set()
    def collect(m):
        require(m not in ('Nyll', 'Nyll.All'), 'Whole NYLL imported by target: ' + m)
        require(m in graph, 'Missing canonical dependency: ' + m)
        if m in selected:
            return
        selected.add(m)
        for d in graph[m]:
            collect(d)
    for m in primary_roots:
        collect(m)
    # Every maintained primary source must be reachable from its existing All.
    primary_modules = {m for m in graph if m not in ('Nyll', 'Nyll.All')
        and m.split('.')[1] in primary}
    require(primary_modules <= selected, 'Primary library aggregate omits source')
    families = {m.split('.')[1] for m in selected}
    ordered = [f for f in order if f in families]
    desired = {m.replace('.', '/') + '.lean': files[m.replace('.', '/') + '.lean']
        for m in selected}
    # Preserve the canonical header and module order. No dependency All is
    # introduced just to expose its unrelated leaves or to schedule CI.
    source_all = files['Nyll/All.lean'].decode()
    desired['Nyll/All.lean'] = ''.join(line for line in source_all.splitlines(True)
        if not line.startswith('import Nyll.') or line.split('.')[1] in primary).replace(
            'Workspace-wide aggregate of all maintained Lean source libraries.',
            'Public entry point for the primary libraries of this extract.').encode()
    desired['Nyll.lean'] = files['Nyll.lean']
    for rel in ('lake-manifest.json', 'lean-toolchain', 'LICENSE'):
        desired[rel] = files[rel]
    new_globs = ['Nyll.All', 'Nyll'] + ['Nyll.' + f + '.+' for f in ordered]
    config, count = re.subn(r'(?ms)^globs = \[.*?^\]',
        'globs = [\n' + ''.join('  "' + g + '",\n' for g in new_globs) + ']',
        files['lakefile.toml'].decode())
    require(count == 1, 'Expected exactly one canonical globs array')
    new_cfg = tomllib.loads(config)
    comparison = json.loads(json.dumps(new_cfg))
    comparison['lean_lib'][0]['globs'] = cfg['lean_lib'][0]['globs']
    require(comparison == cfg, 'Unexpected Lake configuration change')
    desired['lakefile.toml'] = config.encode()
    modules = {module(p) for p in desired if p.endswith('.lean')}
    require([n for n, _, _ in imports(desired['Nyll/All.lean'].decode())] == primary_roots,
        'Extract entry point must import only the ordered primary roots')
    subgraph = {m: (primary_roots if m == 'Nyll.All' else graph[m]) for m in modules}
    seen = set()
    def reach(m):
        require(m in subgraph, 'Extract missing dependency: ' + m)
        if m in seen:
            return
        seen.add(m)
        for d in subgraph[m]:
            reach(d)
    reach('Nyll')
    require(seen == modules == selected | {'Nyll', 'Nyll.All'},
        'Extract differs from exact primary-root import closure')
    # Source-specific provenance documents are selected in the separately
    # reviewed metadata pass; no family-wide document copy is performed here.
    return desired, ordered

OWNER = 'n-yamaguchi-0729'
CANONICAL_REPOSITORY = OWNER + '/NYLL'
PACKAGE = '.github/scripts/publication/'
PUBLICATION = '.github/verification/publication.json'
SAWIN_MANIFEST = '.github/verification/source-manifest.json'
# Audited private planning/operations documents, including their historical paths.
# Keep this explicit: public source and attribution documents are not work plans.
INTERNAL_DOCUMENT_PATHS = {
    'Nyll/AbelianVarieties/IMPLEMENTATION_PLAN.md',
    'Nyll/AlgebraicCurves/LibraryScope.md',
    'Nyll/AlgebraicCurves/SharedLibraryMigrationCandidates.md',
    'Nyll/AnabelianGeometry/FORMALIZATION_STATUS.md',
    'Nyll/ClassFieldTheory/FUNCTION_FIELD_PLAN.md',
    'Nyll/EtaleFundamentalGroups/StacksProjectChapter58.md',
    'Nyll/JacobianVarieties/GENERALIZED_JACOBIAN_IMPLEMENTATION_PLAN.md',
    'Nyll/JacobianVarieties/JV_HANDOFF_2026-10-14.md',
}


def json_bytes(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()


def validate_remote(repo, name):
    expected = 'github.com/' + OWNER + '/' + name
    remote = git(repo, 'remote', 'get-url', 'origin').decode().strip()
    allowed = {'https://' + expected, 'https://' + expected + '.git',
               'git@github.com:' + OWNER + '/' + name + '.git'}
    require(remote in allowed, 'Origin is not the whitelisted repository: ' + name)


def is_internal_document(path):
    """Private workspace instructions are never part of a public extract.

    Match explicit document names, not broad substrings: user-facing README,
    source attribution and license files must not be mistaken for work plans.
    """
    return (Path(path).name in {'AGENTS.md', 'PLAN.md', 'HANDOFF.md', 'ROADMAP.md'}
            or path in INTERNAL_DOCUMENT_PATHS)


def normalized_comparison(path, data):
    # This historical manifest has source SHA fields independent of its content.
    # Actual source, import, configuration, declaration policy and hash fields stay
    # in this comparison: only a newer source SHA cannot create a publication.
    if data is not None and path == SAWIN_MANIFEST:
        value = json.loads(data)
        for key in ('synchronizedFromCommit', 'previousSynchronizedFromCommit'):
            value.pop(key, None)
        return json_bytes(value)
    return data


def changed_items(repo, desired, deletes):
    rows = []
    for rel, data in sorted(desired.items()):
        path = safe_path(repo, rel)
        old = path.read_bytes() if path.exists() else None
        if old != data:
            rows.append({'path': rel, 'action': 'add' if old is None else 'update',
                         'before_sha256': sha(old) if old is not None else None,
                         'after_sha256': sha(data)})
    for rel in sorted(deletes):
        path = safe_path(repo, rel)
        require(path.is_file(), 'Missing tracked deletion: ' + rel)
        rows.append({'path': rel, 'action': 'delete',
                     'before_sha256': sha(path.read_bytes()), 'after_sha256': None})
    return rows


def prepare_repository(name, files, cfg, order, graph, source_imports):
    require(name in PRIMARY, 'Unknown public repository')
    repo = CLONES / name
    require(repo.is_dir() and not repo.is_symlink(), 'Unsafe public checkout: ' + name)
    require_source_clean(repo)
    validate_remote(repo, name)
    require(git(repo, 'branch', '--show-current').decode().strip() == 'main',
            'Public checkout must be on main: ' + name)
    head = git(repo, 'rev-parse', 'HEAD').decode().strip()
    require(head == git(repo, 'rev-parse', 'origin/main').decode().strip(),
            'Public main differs from the fetched origin/main: ' + name)
    primary = PRIMARY[name]
    desired, ordered = desired_extract(files, cfg, order, graph, source_imports, primary)
    source_paths = {p for p in desired if p.endswith('.lean')}
    selected_paths = source_paths - {'Nyll.lean', 'Nyll/All.lean'}
    counts = Counter('EntryPoint' if p in ('Nyll.lean', 'Nyll/All.lean') else p.split('/')[1]
                     for p in source_paths)
    mathlib = next(x for x in cfg['require'] if x['name'] == 'mathlib')
    record = {'repository': name, 'path': str(repo), 'base_head': head,
        'primary_libraries': primary,
        'primary_roots': ['Nyll.' + f + '.All' for f in order if f in primary],
        'canonical_modules': sorted(module(p) for p in selected_paths),
        'ordered_libraries': ordered, 'depths': {f: DEPTH[f] for f in ordered},
        'source_count': len(source_paths), 'owner_counts': dict(sorted(counts.items())),
        'lean_toolchain': files['lean-toolchain'].decode().strip(),
        'mathlib_revision': mathlib['rev'],
        'mathlib_repository': mathlib.get('git', 'https://github.com/leanprover-community/mathlib4'),
        'source_hashes': {p: sha(b) for p, b in sorted(desired.items())},
        'static_checks': {'missing_local_imports': 0, 'reverse_imports': 0,
            'cycles': 0, 'unreachable_sources': 0, 'lake_options_unchanged': True,
            'exact_primary_import_closure': True, 'extra_dependency_aggregates': 0}}
    desired.update(desired_ci(repo, record))
    desired.update(provenance_files(files, selected_paths))
    desired['README.md'] = readme_for_extract((repo / 'README.md').read_text(encoding='utf-8'),
                                             files, selected_paths, primary)
    package_files = {p: data for p, data in files.items() if p.startswith(PACKAGE)}
    require(PACKAGE + 'auto_sync.py' in package_files and PACKAGE + 'public7_sync.py' in package_files,
            'Canonical SHA does not include the publication owner package')
    require(all('__pycache__' not in Path(p).parts and not p.endswith('.pyc') for p in package_files),
            'Compiled Python artifacts must not be distributed')
    desired.update(package_files)
    workflow_source = PACKAGE + 'workflow_templates/auto-sync.yml'
    require(workflow_source in files, 'Canonical auto-sync workflow template is missing')
    desired['.github/workflows/sync-nyll.yml'] = files[workflow_source]
    if name == 'SawinTotallyRealTowers':
        desired.update(desired_sawin(repo, desired, SOURCE, ordered, imports))
        verification_readme = '.github/verification/README.md'
        desired[verification_readme] = sawin_verification_readme(
            (repo / verification_readme).read_text(encoding='utf-8'))
    require(not any(is_internal_document(p) for p in desired),
            'Internal workspace document in publication inputs')
    tracked = set(git(repo, 'ls-files', '-z').decode().rstrip('\0').split('\0'))
    physical = {p.relative_to(repo).as_posix() for p in (repo / 'Nyll').rglob('*.lean')}
    require(physical <= tracked, 'Untracked Lean source in public checkout')
    deletes = {p for p in tracked if p.startswith('Nyll/') and p.endswith('.lean') and p not in desired}
    # These may predate the managed-file inventory. Remove them at every depth,
    # even when they were not recorded by an earlier publication.
    deletes |= {p for p in tracked if is_internal_document(p)}
    deletes |= (set(managed_provenance_paths(files)) & tracked) - set(desired)
    previous = None
    if (repo / PUBLICATION).exists():
        previous = json.loads((repo / PUBLICATION).read_text(encoding='utf-8'))
        require(previous.get('canonical_repository') == CANONICAL_REPOSITORY
                and previous.get('repository') == OWNER + '/' + name,
                'Publication metadata belongs to another repository')
        deletes |= {p for p in previous.get('managed_hashes', {})
                    if p.startswith(PACKAGE) and p in tracked and p not in desired}
    # Check local README/provenance hyperlinks against the resulting tree, including
    # retained directory links, while preserving all mathematical README prose.
    available = (tracked - deletes) | set(desired)
    for rel, data in desired.items():
        if rel.endswith('.md') and not rel.endswith('ANTHROPIC_FLT_ATTRIBUTION.md'):
            require(not local_markdown_links(rel, data, available), 'Broken local Markdown link: ' + rel)
    meaningful = bool(deletes) or any(normalized_comparison(p, safe_path(repo, p).read_bytes()
        if safe_path(repo, p).exists() else None) != normalized_comparison(p, b)
        for p, b in desired.items())
    if not meaningful:
        record.update(changes=[], unchanged=True, applied=False)
        return repo, desired, set(), record
    metadata = {'format_version': 1, 'canonical_repository': CANONICAL_REPOSITORY,
        'repository': OWNER + '/' + name, 'source_commit': SOURCE,
        'primaryRoots': record['primary_roots'],
        'source_hashes': record['source_hashes'],
        'managed_hashes': {p: sha(b) for p, b in sorted(desired.items())}}
    desired[PUBLICATION] = json_bytes(metadata)
    record.update(changes=changed_items(repo, desired, deletes), unchanged=False, applied=False)
    return repo, desired, deletes, record


def prepare(names):
    files, cfg, order, graph, source_imports = canonical()
    return [prepare_repository(name, files, cfg, order, graph, source_imports) for name in names]


def apply_prepared(prepared):
    # Validate every preimage and HEAD before writing the first repository.
    for repo, desired, deletes, record in prepared:
        require_source_clean(repo)
        validate_remote(repo, record['repository'])
        require(git(repo, 'rev-parse', 'HEAD').decode().strip() == record['base_head'], 'HEAD changed')
        for item in record['changes']:
            path = safe_path(repo, item['path'])
            old = path.read_bytes() if path.exists() else None
            require((sha(old) if old is not None else None) == item['before_sha256'],
                    'File preimage changed: ' + item['path'])
    for repo, desired, deletes, record in prepared:
        if record['unchanged']:
            continue
        for item in record['changes']:
            path = safe_path(repo, item['path'])
            if item['action'] == 'delete':
                path.unlink()
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(desired[item['path']])
        for rel, data in desired.items():
            require(safe_path(repo, rel).read_bytes() == data, 'Postimage mismatch: ' + rel)
        actual = {p.relative_to(repo).as_posix() for p in (repo / 'Nyll').rglob('*.lean')}
        require(actual == {p for p in desired if p.startswith('Nyll/') and p.endswith('.lean')},
                'Physical source set differs after apply')
        require(all(not safe_path(repo, p).exists() for p in deletes), 'A deleted path survived')
        record['applied'] = True


def configure(root, clones, source):
    global ROOT, CLONES, SOURCE
    ROOT, CLONES, SOURCE = Path(root).resolve(), Path(clones).resolve(), source
    require(re.fullmatch('[0-9a-f]{40}', SOURCE), 'Source must be an immutable full commit SHA')
    require(ROOT != CLONES and not CLONES.is_relative_to(ROOT / 'Nyll'),
            'Public checkouts overlap canonical source')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--clones', type=Path, required=True)
    parser.add_argument('--source', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repository', choices=sorted(PRIMARY))
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    configure(args.root, args.clones, args.source)
    output = args.output.resolve()
    require(output != ROOT and not output.is_relative_to(ROOT / 'Nyll')
            and not output.is_relative_to(CLONES), 'Report directory overlaps managed source')
    output.mkdir(parents=True, exist_ok=True)
    prepared = prepare([args.repository] if args.repository else list(PRIMARY))
    report = {'source_commit': SOURCE, 'mode': 'apply' if args.apply else 'plan',
        'source_tree': git(ROOT, 'rev-parse', SOURCE + '^{tree}').decode().strip(),
        'builds_run': False, 'repositories': [x[3] for x in prepared]}
    (output / 'public7-plan.json').write_bytes(json_bytes(report))
    if args.apply:
        apply_prepared(prepared)
        (output / 'public7-result.json').write_bytes(json_bytes(report))
    print(json.dumps({'source_commit': SOURCE, 'mode': report['mode'],
        'repositories': [{'repository': r['repository'], 'source_count': r['source_count'],
            'changes': len(r['changes']), 'unchanged': r['unchanged'], 'applied': r['applied']}
            for r in report['repositories']]}, indent=2))


if __name__ == '__main__':
    main()
