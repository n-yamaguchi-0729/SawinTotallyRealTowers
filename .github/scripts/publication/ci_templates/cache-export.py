#!/usr/bin/env python3
"""Export and restore source-matched public Lean proof artifacts without compiling.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import subprocess
import tarfile

CONFIGS = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')
LIB_SUFFIXES = ('.olean', '.olean.hash', '.olean.private', '.olean.private.hash',
                '.olean.server', '.olean.server.hash', '.ilean', '.ilean.hash', '.trace')
IR_SUFFIXES = ('.c', '.c.hash', '.bc', '.bc.hash', '.ir', '.ir.hash')
CHUNK_BYTES = 512 * 1024 * 1024


def digest(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()


def source_paths(root):
    paths = sorted(root.glob('Nyll/**/*.lean'))
    if (root / 'Nyll.lean').is_file():
        paths.append(root / 'Nyll.lean')
    if not paths:
        raise ValueError('No public Nyll sources')
    for path in paths:
        if path.is_symlink() or not path.resolve().is_relative_to(root):
            raise ValueError('Symlink or escaped source')
    return paths


def source_hashes(root):
    return {str(path.relative_to(root).as_posix()): digest(path)
            for path in source_paths(root)}


def allowed_paths(sources):
    allowed = set()
    for source in sources:
        base = source.removesuffix('.lean')
        allowed.update('.lake/build/lib/lean/' + base + suffix for suffix in LIB_SUFFIXES)
        allowed.update('.lake/build/ir/' + base + suffix for suffix in IR_SUFFIXES)
    return allowed


def safe_file(root, name):
    rel = PurePosixPath(name)
    if rel.is_absolute() or '..' in rel.parts or '\\' in name:
        raise ValueError('Unsafe artifact path')
    path = root.joinpath(*rel.parts)
    if any(p.is_symlink() for p in (path, *path.parents)) or not path.resolve().is_relative_to(root):
        raise ValueError('Symlink or escaped artifact')
    return path


def package(root, output, sha, run_url, lean_version):
    sources = source_hashes(root)
    configurations = {name: digest(root / name) for name in CONFIGS}
    allowed = allowed_paths(sources)
    required = {'.lake/build/lib/lean/' + name.removesuffix('.lean') + '.olean' for name in sources}
    missing = sorted(name for name in required if not safe_file(root, name).is_file())
    if missing:
        raise ValueError('Incomplete final cache: ' + ', '.join(missing[:8]))
    artifacts = {}
    for name in sorted(allowed):
        path = safe_file(root, name)
        if path.is_file():
            artifacts[name] = {'sha256': digest(path), 'size': path.stat().st_size}
    output.mkdir(parents=True, exist_ok=False)
    groups, group, size = [], [], 0
    for name, record in artifacts.items():
        if record['size'] > CHUNK_BYTES:
            raise ValueError('One artifact exceeds the bounded archive size')
        if group and size + record['size'] > CHUNK_BYTES:
            groups.append(group)
            group, size = [], 0
        group.append(name)
        size += record['size']
    if group:
        groups.append(group)
    archives = []
    for number, members in enumerate(groups, 1):
        name = f'proof-cache-{number:03d}.tar.gz'
        archive = output / name
        with tarfile.open(archive, 'w:gz', compresslevel=3) as tar:
            for member in members:
                path = safe_file(root, member)
                info = tar.gettarinfo(path, arcname=member)
                info.uid = info.gid = info.mtime = 0
                info.uname = info.gname = ''
                info.mode = 0o644
                with path.open('rb') as stream:
                    tar.addfile(info, stream)
                if digest(path) != artifacts[member]['sha256']:
                    raise ValueError('Artifact changed while exporting')
        if archive.stat().st_size >= 2 * 1024 ** 3:
            raise ValueError('Release asset exceeds GitHub size limit')
        archives.append({'name': name, 'sha256': digest(archive), 'size': archive.stat().st_size,
                         'members': members})
    if sources != source_hashes(root) or configurations != {n: digest(root / n) for n in CONFIGS}:
        raise ValueError('Source/configuration changed during export')
    manifest = {'schema': 'nyll-public-proof-cache-v1', 'commit': sha, 'workflowRun': run_url,
                'producer': {'system': platform.system(), 'machine': platform.machine(),
                             'leanVersion': lean_version},
                'leanToolchain': (root / 'lean-toolchain').read_text().strip(),
                'compatibility': 'Same source/configuration and producer platform only; dependencies are separate.',
                'sources': sources, 'configuration': configurations,
                'artifacts': artifacts, 'archives': archives}
    (output / 'cache-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    return manifest


def validate(root, directory):
    manifest = json.loads((directory / 'cache-manifest.json').read_text())
    if manifest.get('schema') != 'nyll-public-proof-cache-v1':
        raise ValueError('Unsupported cache manifest')
    if manifest['sources'] != source_hashes(root):
        raise ValueError('Cache sources do not match this checkout')
    if manifest['configuration'] != {name: digest(root / name) for name in CONFIGS}:
        raise ValueError('Cache toolchain/dependency/build configuration mismatch')
    if (manifest['producer']['system'], manifest['producer']['machine']) != (platform.system(), platform.machine()):
        raise ValueError('Cache producer platform differs from this host')
    version = subprocess.check_output(['lean', '--version'], cwd=root, text=True).strip()
    if version != manifest['producer']['leanVersion']:
        raise ValueError('Installed Lean compiler does not match cache producer')
    allowed = allowed_paths(manifest['sources'])
    if not set(manifest['artifacts']) <= allowed:
        raise ValueError('Manifest contains an unsupported artifact')
    seen = set()
    for archive in manifest['archives']:
        name = archive['name']
        if Path(name).name != name or not name.endswith('.tar.gz'):
            raise ValueError('Unsafe archive name')
        path = directory / name
        if path.is_symlink() or digest(path) != archive['sha256'] or path.stat().st_size != archive['size']:
            raise ValueError('Archive checksum/size mismatch')
        expected = set(archive['members'])
        if len(expected) != len(archive['members']) or seen & expected or not expected <= allowed:
            raise ValueError('Invalid archive member index')
        actual = set()
        with tarfile.open(path, 'r:gz') as tar:
            for member in tar:
                if not member.isfile() or member.name not in expected or member.name in actual:
                    raise ValueError('Unexpected archive member')
                record = manifest['artifacts'][member.name]
                stream = tar.extractfile(member)
                value = hashlib.sha256()
                for block in iter(lambda: stream.read(1024 * 1024), b''):
                    value.update(block)
                if member.size != record['size'] or value.hexdigest() != record['sha256']:
                    raise ValueError('Artifact checksum/size mismatch')
                safe_file(root, member.name)
                actual.add(member.name)
        if actual != expected:
            raise ValueError('Archive is missing indexed members')
        seen.update(actual)
    if seen != set(manifest['artifacts']):
        raise ValueError('Incomplete archive index')
    return manifest


def restore(root, directory):
    manifest = validate(root, directory)
    wanted = set()
    for name, record in manifest['artifacts'].items():
        path = safe_file(root, name)
        if path.exists():
            if not path.is_file() or digest(path) != record['sha256']:
                raise ValueError('Existing different output preserved: ' + name)
        else:
            wanted.add(name)
    for archive in manifest['archives']:
        with tarfile.open(directory / archive['name'], 'r:gz') as tar:
            for member in tar:
                if member.name not in wanted:
                    continue
                path = safe_file(root, member.name)
                path.parent.mkdir(parents=True, exist_ok=True)
                # Exclusive creation never replaces a concurrent/local output.
                with path.open('xb') as destination, tar.extractfile(member) as source:
                    for block in iter(lambda: source.read(1024 * 1024), b''):
                        destination.write(block)
    return len(wanted)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('package', 'verify', 'restore'))
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--directory', type=Path, required=True)
    args = parser.parse_args()
    root, directory = args.root.resolve(), args.directory.resolve()
    if args.mode == 'package':
        if os.environ.get('GITHUB_ACTIONS') != 'true' or os.environ.get('GITHUB_REF') != 'refs/heads/main':
            raise ValueError('Distribution packaging requires a successful main CI caller')
        sha = os.environ['GITHUB_SHA']
        current = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
        if sha != current:
            raise ValueError('Checkout does not match workflow commit')
        subprocess.run(['git', 'diff', '--exit-code', '--quiet', 'HEAD', '--', 'Nyll', 'Nyll.lean', *CONFIGS], cwd=root, check=True)
        version = subprocess.check_output(['lean', '--version'], cwd=root, text=True).strip()
        run_url = f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}"
        manifest = package(root, directory, sha, run_url, version)
        print(json.dumps({'modules': len(manifest['sources']), 'artifacts': len(manifest['artifacts']), 'archives': len(manifest['archives'])}))
    elif args.mode == 'verify':
        manifest = validate(root, directory)
        print(f"Verified {len(manifest['artifacts'])} artifacts; no compilation performed.")
    else:
        print(f'Restored {restore(root, directory)} missing artifacts; existing outputs preserved.')


if __name__ == '__main__':
    main()
