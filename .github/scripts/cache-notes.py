#!/usr/bin/env python3
"""Render cache download instructions and update only the matching release body.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
"""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import re
from urllib.error import HTTPError
from urllib.request import Request, urlopen


def identity(repository, sha):
    if not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository):
        raise ValueError('Invalid repository')
    if not re.fullmatch(r'[0-9a-f]{40}', sha):
        raise ValueError('Invalid commit')
    return f'cache-{sha}-linux-x86_64'


def render(repository, sha):
    tag = identity(repository, sha)
    return (f'Prebuilt Lean cache for `{sha}` (Linux x86_64).\n\n'
            'From a checkout of this commit, with its pinned Lean toolchain installed:\n\n'
            '```sh\n'
            'lake exe cache get\n'
            f'gh release download {tag} -R {repository} -D tmp/proof-cache-{sha[:12]}\n'
            f'python3 -B .github/scripts/cache-export.py restore --directory tmp/proof-cache-{sha[:12]}\n'
            '```\n')


def completed_main_commit(event, repository):
    repo = event.get('repository', {})
    run = event.get('workflow_run', {})
    if (repo.get('full_name') != repository or repo.get('private') is not False
            or repo.get('default_branch') != 'main'
            or run.get('head_repository', {}).get('full_name') != repository
            or run.get('head_branch') != 'main' or run.get('status') != 'completed'
            or run.get('conclusion') != 'success'
            or run.get('event') not in ('push', 'workflow_dispatch')
            or run.get('name') not in ('Lean', 'Verify Sawin theorem')
            or run.get('path') not in ('.github/workflows/lean.yml', '.github/workflows/libraries.yml')):
        return None
    sha = run.get('head_sha', '')
    identity(repository, sha)
    return sha


def github_api(repository, endpoint, token, payload=None):
    request = Request('https://api.github.com/repos/' + repository + endpoint,
                      data=json.dumps(payload).encode() if payload is not None else None,
                      method='PATCH' if payload is not None else 'GET',
                      headers={'Authorization': 'Bearer ' + token,
                               'Accept': 'application/vnd.github+json',
                               'X-GitHub-Api-Version': '2022-11-28',
                               'Content-Type': 'application/json',
                               'User-Agent': 'nyll-cache-instructions'})
    try:
        with urlopen(request, timeout=30) as response:
            return json.load(response)
    except HTTPError as error:
        if error.code == 404 and payload is None:
            return None
        raise RuntimeError(f'GitHub request failed (HTTP {error.code})') from None


def update(event, repository, token, api=github_api):
    sha = completed_main_commit(event, repository)
    if sha is None:
        return False
    tag = identity(repository, sha)
    release = api(repository, '/releases/tags/' + tag, token)
    if release is None:
        return False
    if (release.get('tag_name') != tag or release.get('target_commitish') != sha
            or release.get('draft') is not False
            or not isinstance(release.get('id'), int)):
        raise ValueError('Release does not match the completed workflow commit')
    body = render(repository, sha)
    if release.get('body') != body:
        api(repository, '/releases/' + str(release['id']), token, {'body': body})
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('render', 'update'))
    parser.add_argument('--repository', default=os.environ.get('GITHUB_REPOSITORY'))
    parser.add_argument('--sha', default=os.environ.get('GITHUB_SHA'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.mode == 'render':
        text = render(args.repository, args.sha)
        if args.output:
            args.output.write_text(text)
        else:
            print(text, end='')
    else:
        if os.environ.get('GITHUB_EVENT_NAME') != 'workflow_run':
            raise ValueError('Release text update requires workflow_run')
        event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
        update(event, args.repository, os.environ['GH_TOKEN'])


if __name__ == '__main__':
    main()
