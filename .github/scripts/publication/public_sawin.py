# Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
# Released under Apache 2.0. Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
"""Refresh Sawin's existing exact-source receipt without changing proof policy."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import tomllib


def refresh_reviewed_source(row, previous, current, source_commit):
    """Admit only an explicitly reviewed source transition, preserving its history."""
    sha = lambda data: hashlib.sha256(data).hexdigest()
    changes = json.loads((Path(__file__).with_name('sawin-reviewed-source-updates.json'))
                         .read_text(encoding='utf-8'))['reviewedSourceChanges']
    matches = [x for x in changes if x['path'] == row['sourcePath']
               and x['old'] == row['currentSourceSHA256'] == sha(previous)
               and x['new'] == sha(current)]
    if len(matches) != 1:
        raise ValueError('Historical partial source changed; audit required: ' + row['sourcePath'])
    update = matches[0]
    length = row['copyrightHeaderByteLength']
    if not (previous[:length] == current[:length]
            and sha(current[:length]) == row['copyrightHeaderSHA256']
            and sha(previous[length:]) == update['old_body_sha256']
            == row.get('currentBodySHA256', row['historicalBodySHA256'])
            and sha(current[length:]) == update['current_body_sha256']
            and update['recursive_parent_declaration_unchanged'] is True):
        raise ValueError('Reviewed partial source/header evidence differs: ' + row['sourcePath'])
    row.setdefault('reviewedSourceUpdates', []).append({
        'previousCanonicalSource': row.get('canonicalSource'),
        'previousSourceSHA256': sha(previous), 'previousBodySHA256': sha(previous[length:]),
        'sourceSHA256': sha(current), 'bodySHA256': sha(current[length:]),
        'recursiveParentDeclarationUnchanged': True,
        'changedProofDeclarations': update['changed_proofs']})
    row['currentSourceSHA256'] = sha(current)
    row['currentBodySHA256'] = sha(current[length:])
    row['canonicalSource'] = {'repository': 'https://github.com/n-yamaguchi-0729/NYLL',
        'commit': source_commit, 'path': row['sourcePath'], 'sourceSHA256': sha(current)}


def desired_sawin(repo, desired, source_commit, ordered, parse_imports):
    """Return only the refreshed pinned manifest and its existing verifier."""
    if repo.name != "SawinTotallyRealTowers":
        return {}
    manifest_path = ".github/verification/source-manifest.json"
    checker_path = ".github/verification/check_source_closure.py"
    manifest = json.loads((repo / manifest_path).read_text(encoding="utf-8"))
    rows = {}
    for path, data in sorted(desired.items()):
        if not path.endswith(".lean"):
            continue
        module = path[:-5].replace("/", ".")
        rows[module] = {
            "owner": "EntryPoint" if module in ("Nyll", "Nyll.All") else module.split(".")[1],
            "path": path,
            "sha256": hashlib.sha256(data).hexdigest(),
            "imports": [name for name, _, _ in parse_imports(data.decode())],
        }
    owners = dict(sorted(Counter(row["owner"] for row in rows.values()).items()))
    cfg = tomllib.loads(desired["lakefile.toml"].decode())
    mathlib = next(dep["rev"] for dep in cfg["require"] if dep["name"] == "mathlib")
    toolchain = desired["lean-toolchain"].decode().strip()
    manifest.update(synchronizedFromCommit=source_commit, moduleCount=len(rows),
        ownerCounts=owners, moduleRows=rows, leanToolchain=toolchain, mathlibRevision=mathlib)
    # sourceCommit is the historical admission; do not rewrite it as new evidence.
    checker = (repo / checker_path).read_text(encoding="utf-8")
    replacements = [
        (r"(?m)^OWNERS = .*?$", "OWNERS = " + repr(owners)),
        (r"(?m)^MATHLIB = .*?$", "MATHLIB = " + repr(mathlib)),
        (r"(?m)^TOOLCHAIN = .*?$", "TOOLCHAIN = " + repr(toolchain)),
        (r"(?ms)^    ordered = \[.*?\]", "    ordered = " + repr(ordered)),
    ]
    for pattern, replacement in replacements:
        checker, count = re.subn(pattern, lambda _: replacement, checker)
        if count != 1:
            raise ValueError("Sawin verifier format changed: " + pattern)
    compile(checker, checker_path, "exec")
    baseline_path = ".github/verification/historical-partial-baseline.json"
    baseline = json.loads((repo / baseline_path).read_text(encoding="utf-8"))
    retained = [row for row in baseline["allowedPartialDeclarations"]
                if row["originModule"] in rows]
    for row in retained:
        if row["currentSourceSHA256"] != rows[row["originModule"]]["sha256"]:
            refresh_reviewed_source(row, (repo / row['sourcePath']).read_bytes(),
                                    desired[row['sourcePath']], source_commit)
    baseline.update(allowedPartialDeclarations=retained, selectedCount=len(retained),
        purpose="Previously admitted compiler-generated partial declarations whose original modules "
                "remain in this exact source closure. Original declaration, source, header, body, "
                "and historical admission hashes are preserved; the compiled inventory must match "
                "this complete selected set.")
    verify_path = ".github/verification/verify.py"
    verify = (repo / verify_path).read_text(encoding="utf-8")
    old_check = "require(len(baseline['allowedPartialDeclarations']) == 31, 'Expected exactly 31 inventoried compiler-generated partials')"
    new_check = "require(len(baseline['allowedPartialDeclarations']) == baseline['selectedCount'], 'Historical partial selection/count mismatch')"
    if old_check in verify:
        verify = verify.replace(old_check, new_check)
    elif new_check not in verify:
        raise ValueError("Historical partial verifier changed")
    old_body_check = "== old['historicalBodySHA256']"
    new_body_check = "== old.get('currentBodySHA256', old['historicalBodySHA256'])"
    if old_body_check in verify:
        if verify.count(old_body_check) != 1:
            raise ValueError('Historical partial body check is ambiguous')
        verify = verify.replace(old_body_check, new_body_check)
    elif new_body_check not in verify:
        raise ValueError('Historical partial body verifier changed')
    test_path = "tests/test_verification.py"
    tests = (repo / test_path).read_text(encoding="utf-8")
    old_test = "self.assertEqual(len(baseline['allowedPartialDeclarations']), 31)"
    new_test = "self.assertEqual(len(baseline['allowedPartialDeclarations']), baseline['selectedCount'])"
    if old_test in tests:
        tests = tests.replace(old_test, new_test)
    elif new_test not in tests:
        raise ValueError("Historical partial test changed")
    old_body_test = "old['historicalBodySHA256'])"
    new_body_test = "old.get('currentBodySHA256', old['historicalBodySHA256']))"
    if new_body_test not in tests:
        if tests.count(old_body_test) != 1:
            raise ValueError('Historical partial body test is ambiguous')
        tests = tests.replace(old_body_test, new_body_test)
    compile(verify, verify_path, "exec")
    compile(tests, test_path, "exec")
    return {
        baseline_path: (json.dumps(baseline, indent=2) + "\n").encode(),
        verify_path: verify.encode(), test_path: tests.encode(),
        manifest_path: (json.dumps(manifest, indent=2) + "\n").encode(),
        checker_path: checker.encode(),
    }
