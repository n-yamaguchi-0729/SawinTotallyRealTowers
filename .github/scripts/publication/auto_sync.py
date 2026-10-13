#!/usr/bin/env python3
"""Update one public extract from a verified, non-rewinding NYLL main commit.

Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0. Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.error
import urllib.parse
import urllib.request

from public7_sync import OWNER, PRIMARY, CANONICAL_REPOSITORY, PUBLICATION, PACKAGE

SOURCE_WORKFLOW = 'libraries.yml'
SHA = re.compile(r'[0-9a-f]{40}')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def repository_name(full_name):
    prefix = OWNER + '/'
    require(full_name.startswith(prefix) and full_name[len(prefix):] in PRIMARY,
            'Repository is not one of the seven configured public libraries')
    return full_name[len(prefix):]


class GitHub:
    def __init__(self, token):
        self.token = token

    def request(self, path, method='GET', body=None):
        require(path.startswith('/repos/' + OWNER + '/'), 'Unexpected GitHub API path')
        headers = {'Accept': 'application/vnd.github+json',
                   'X-GitHub-Api-Version': '2022-11-28',
                   'User-Agent': 'NYLL-publication'}
        if self.token:
            headers['Authorization'] = 'Bearer ' + self.token
        data = json.dumps(body).encode() if body is not None else None
        request = urllib.request.Request('https://api.github.com' + path,
                                         data=data, headers=headers, method=method)
        try:
            with urllib.request.urlopen(request, timeout=60) as response:
                payload = response.read()
                return json.loads(payload) if payload else None
        except urllib.error.HTTPError as error:
            raise RuntimeError('GitHub API request failed (HTTP ' + str(error.code) + ')') from None
        except urllib.error.URLError:
            raise RuntimeError('GitHub API request failed (network)') from None

    def main_sha(self, repository):
        value = self.request('/repos/' + repository + '/git/ref/heads/main')
        commit = value.get('object', {}).get('sha', '')
        require(value.get('ref') == 'refs/heads/main' and SHA.fullmatch(commit),
                'GitHub main response does not identify a commit')
        return commit


def trusted_success(runs, source_sha, workflow_id):
    """Accept only the newest matching trusted run/attempt, never a PR or fork."""
    matching = [run for run in runs
        if run.get('head_sha') == source_sha
        and run.get('head_branch') == 'main'
        and run.get('workflow_id') == workflow_id
        and run.get('path') == '.github/workflows/' + SOURCE_WORKFLOW
        and run.get('event') in ('push', 'workflow_dispatch')
        and run.get('repository', {}).get('full_name') == CANONICAL_REPOSITORY
        and run.get('head_repository', {}).get('full_name') == CANONICAL_REPOSITORY]
    if not matching:
        return False
    latest = max(matching, key=lambda run: (int(run['id']), int(run.get('run_attempt', 1))))
    return latest.get('status') == 'completed' and latest.get('conclusion') == 'success'


def verified_main(api):
    source_sha = api.main_sha(CANONICAL_REPOSITORY)
    prefix = '/repos/' + CANONICAL_REPOSITORY + '/actions/workflows/' + SOURCE_WORKFLOW
    workflow = api.request(prefix)
    require(workflow.get('path') == '.github/workflows/' + SOURCE_WORKFLOW,
            'Source workflow is not the configured Lean validation workflow')
    query = urllib.parse.urlencode({'branch': 'main', 'head_sha': source_sha, 'per_page': 100})
    runs = api.request(prefix + '/runs?' + query).get('workflow_runs', [])
    if not trusted_success(runs, source_sha, workflow['id']):
        return None
    require(api.main_sha(CANONICAL_REPOSITORY) == source_sha,
            'NYLL main changed while its verification was inspected')
    return source_sha


def ensure_public_lean(api, repository, commit, apply):
    """Recover a lost post-push dispatch; an existing failure is not retried."""
    if not apply:
        return False
    prefix = '/repos/' + repository + '/actions/workflows/lean.yml'
    query = urllib.parse.urlencode({'branch': 'main', 'head_sha': commit, 'per_page': 100})
    runs = api.request(prefix + '/runs?' + query).get('workflow_runs', [])
    if any(run.get('head_sha') == commit and run.get('head_branch') == 'main'
           and run.get('path') == '.github/workflows/lean.yml'
           and run.get('event') in ('push', 'workflow_dispatch')
           and run.get('repository', {}).get('full_name') == repository
           and run.get('head_repository', {}).get('full_name') == repository for run in runs):
        return False
    require(api.main_sha(repository) == commit, 'Public main changed before its Lean dispatch')
    api.request(prefix + '/dispatches', method='POST', body={'ref': 'main'})
    return True


def git(repo, *arguments, env=None, allowed=(0,)):
    result = subprocess.run(['git', '-C', str(repo), *arguments],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)
    require(result.returncode in allowed, 'Git operation failed: ' + arguments[0])
    return result


def safe_file(repo, relative):
    path = Path(relative)
    require(relative and not path.is_absolute() and '..' not in path.parts
            and '\\' not in relative and path.parts[0] != '.git', 'Unsafe managed path')
    target = repo / path
    require(target.resolve().is_relative_to(repo.resolve()), 'Managed path leaves checkout')
    require(not any(part.is_symlink() for part in [target, *target.parents]
                    if part != repo.parent), 'Managed path contains a symbolic link')
    return target


def validate_checkout(repo, name, expected_sha):
    require(repo.name == name and repo.is_dir() and not repo.is_symlink(),
            'Target checkout must be a directory named for the selected repository')
    remote = git(repo, 'remote', 'get-url', 'origin').stdout.decode().strip()
    require(remote in {'https://github.com/' + OWNER + '/' + name,
                       'https://github.com/' + OWNER + '/' + name + '.git'},
            'Target origin is not the exact public repository')
    require(git(repo, 'branch', '--show-current').stdout.decode().strip() == 'main',
            'Target checkout is not on main')
    require(git(repo, 'rev-parse', 'HEAD').stdout.decode().strip() == expected_sha,
            'Target HEAD differs from current remote main')
    require(not git(repo, 'status', '--porcelain=v1', '--untracked-files=all').stdout,
            'Target checkout has local changes')
    remote_main = git(repo, 'ls-remote', 'origin', 'refs/heads/main').stdout.decode().split()
    require(remote_main == [expected_sha, 'refs/heads/main'], 'Target remote main changed')


def previous_snapshot(repo, repository):
    path = safe_file(repo, PUBLICATION)
    if not path.is_file():
        return None
    metadata = json.loads(path.read_text(encoding='utf-8'))
    require(metadata.get('canonical_repository') == CANONICAL_REPOSITORY
            and metadata.get('repository') == repository
            and SHA.fullmatch(metadata.get('source_commit', '')),
            'Publication metadata does not identify this repository and source')
    hashes = metadata.get('managed_hashes', {})
    require(bool(hashes), 'Publication metadata has no managed file inventory')
    for relative, expected in hashes.items():
        path = safe_file(repo, relative)
        require(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == expected,
                'Managed file differs from its published inventory: ' + relative)
    return metadata


def auth_environment(token):
    require(bool(token), 'A GitHub Actions token is required to publish')
    env = {key: value for key, value in os.environ.items()
           if key != 'GIT_CONFIG_COUNT' and not re.fullmatch(r'GIT_CONFIG_(KEY|VALUE)_\d+', key)
           and not key.startswith('GIT_TRACE') and key not in ('GIT_CURL_VERBOSE', 'GIT_CONFIG_PARAMETERS')}
    env['GIT_CONFIG_COUNT'] = '1'
    env['GIT_CONFIG_KEY_0'] = 'http.https://github.com/.extraheader'
    env['GIT_CONFIG_VALUE_0'] = 'AUTHORIZATION: basic ' + base64.b64encode(
        ('x-access-token:' + token).encode()).decode()
    env['GIT_TERMINAL_PROMPT'] = '0'
    return env


def execute(repository, checkout, workdir, apply=False, api=None):
    name = repository_name(repository)
    repo = Path(checkout).absolute()
    api = api or GitHub(os.environ.get('GITHUB_TOKEN', ''))
    require(not apply or bool(getattr(api, 'token', '')),
            'A GitHub Actions token is required before applying a publication')
    base_head = api.main_sha(repository)
    validate_checkout(repo, name, base_head)
    previous = previous_snapshot(repo, repository)
    if previous is None:
        return {'status': 'skipped', 'reason': 'Manual publication bootstrap is required'}
    source_sha = verified_main(api)
    if source_sha is None:
        return {'status': 'skipped', 'reason': 'Current NYLL main has no successful trusted Lean run'}
    if previous['source_commit'] == source_sha:
        dispatched = ensure_public_lean(api, repository, base_head, apply)
        return {'status': 'unchanged', 'source_commit': source_sha, 'lean_dispatched': dispatched}
    scratch = Path(workdir).absolute()
    require(not scratch.is_relative_to(repo) and not repo.is_relative_to(scratch),
            'Work directory overlaps the target checkout')
    scratch.mkdir(parents=True, exist_ok=False)
    source = scratch / 'NYLL'
    source.mkdir()
    git(source, 'init', '--quiet')
    git(source, 'remote', 'add', 'origin', 'https://github.com/' + CANONICAL_REPOSITORY + '.git')
    git(source, 'fetch', '--quiet', '--filter=blob:none', '--no-tags', 'origin',
        source_sha, previous['source_commit'])
    ancestry = git(source, 'merge-base', '--is-ancestor', previous['source_commit'],
                   source_sha, allowed=(0, 1))
    if ancestry.returncode == 1:
        return {'status': 'skipped', 'reason': 'NYLL main does not contain the published source'}
    git(source, 'checkout', '--quiet', '--detach', source_sha)
    pipeline = source / PACKAGE / 'public7_sync.py'
    require(pipeline.is_file(), 'Verified source does not contain the publication owner package')
    require(api.main_sha(CANONICAL_REPOSITORY) == source_sha
            and api.main_sha(repository) == base_head, 'A main branch changed before extraction')
    output = scratch / 'result'
    command = [sys.executable, '-B', str(pipeline), '--root', str(source),
               '--clones', str(repo.parent), '--repository', name, '--source', source_sha,
               '--output', str(output)]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(result.returncode == 0, 'Verified publication pipeline failed; checkout remains unpushed')
    report = json.loads((output / 'public7-plan.json').read_text(encoding='utf-8'))
    require(report.get('source_commit') == source_sha and len(report.get('repositories', [])) == 1,
            'Publication report is not for this exact source and target')
    record = report['repositories'][0]
    require(record.get('repository') == name and record.get('base_head') == base_head,
            'Publication report base HEAD or repository changed')
    if record.get('unchanged'):
        dispatched = ensure_public_lean(api, repository, base_head, apply)
        return {'status': 'unchanged', 'source_commit': previous['source_commit'],
                'lean_dispatched': dispatched}
    workflow_changes = [item['path'] for item in record['changes']
                        if item['path'].startswith('.github/workflows/')]
    if workflow_changes:
        # GITHUB_TOKEN has no Workflows(write) permission. Keep the checkout clean
        # and request ordinary manual publication for this CI maintenance change.
        return {'status': 'skipped', 'reason': 'Workflow changes require manual publication',
                'workflow_changes': workflow_changes, 'source_commit': source_sha}
    if not apply:
        return {'status': 'planned', 'source_commit': source_sha, 'changes': len(record['changes'])}
    require(api.main_sha(CANONICAL_REPOSITORY) == source_sha
            and api.main_sha(repository) == base_head, 'A main branch changed before application')
    result = subprocess.run([*command, '--apply'], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(result.returncode == 0, 'Verified publication apply failed; checkout remains unpushed')
    applied = json.loads((output / 'public7-result.json').read_text(encoding='utf-8'))
    require(applied.get('source_commit') == source_sha and len(applied.get('repositories', [])) == 1,
            'Applied publication report does not identify the exact source and target')
    applied_record = applied['repositories'][0]
    require(applied_record.get('applied') is True and applied_record.get('changes') == record['changes']
            and applied_record.get('base_head') == base_head and applied_record.get('repository') == name,
            'Applied publication differs from its plan')
    require(api.main_sha(CANONICAL_REPOSITORY) == source_sha
            and api.main_sha(repository) == base_head, 'A main branch changed before publication')
    require(git(repo, 'rev-parse', 'HEAD').stdout.decode().strip() == base_head,
            'Target HEAD changed during extraction')
    paths = [item['path'] for item in record['changes']]
    require(bool(paths) and len(paths) == len(set(paths)), 'Publication paths are empty or duplicated')
    for relative in paths:
        safe_file(repo, relative)
    for offset in range(0, len(paths), 200):
        git(repo, 'add', '--', *paths[offset:offset + 200])
    staged = git(repo, 'diff', '--cached', '--name-only', '-z').stdout.decode().rstrip('\0').split('\0')
    require(set(staged) == set(paths), 'Staged paths differ from the reviewed publication plan')
    git(repo, '-c', 'user.name=github-actions[bot]', '-c',
        'user.email=41898282+github-actions[bot]@users.noreply.github.com',
        'commit', '--quiet', '-m', 'Sync verified NYLL ' + source_sha[:12])
    commit = git(repo, 'rev-parse', 'HEAD').stdout.decode().strip()
    git(repo, 'push', 'origin', 'HEAD:refs/heads/main', env=auth_environment(api.token))
    require(api.main_sha(repository) == commit, 'Remote main does not match the published commit')
    dispatched = ensure_public_lean(api, repository, commit, True)
    return {'status': 'published', 'source_commit': source_sha, 'commit': commit,
            'lean_dispatched': dispatched}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', required=True)
    parser.add_argument('--checkout', type=Path, required=True)
    parser.add_argument('--workdir', type=Path, required=True)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    try:
        print(json.dumps(execute(args.repository, args.checkout, args.workdir, args.apply), indent=2))
    except (ValueError, RuntimeError, OSError, KeyError) as error:
        # No subprocess stderr, request headers, credentials or environment dump.
        print(json.dumps({'status': 'failed', 'reason': str(error)}), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
