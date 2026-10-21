#!/usr/bin/env python3
"""Audit the full physical tree before dividing proof checks by import closure.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
"""
from pathlib import Path
import argparse
import json
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci_templates"))
import generate_manifest


def pure_imports(text):
    """The two global entry files must contain imports and comments only.

    Masking strings/quoted names is insufficient here: a string alone must not
    be mistaken for an empty body. Remove only correctly nested comments.
    """
    result, i, depth = [], 0, 0
    while i < len(text):
        if not depth and text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("/-", i):
            depth += 1
            result.append(" ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        else:
            result.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unterminated aggregate comment")
    tokens = "".join(result).split()
    if len(tokens) % 2 or any(tokens[i] != "import" or
                             not generate_manifest.valid_name(tokens[i + 1])
                             for i in range(0, len(tokens), 2)):
        raise ValueError("Global entry contains declarations or unsupported commands")
    return tokens[1::2]


def partition(root, manifest, config):
    rows = manifest["moduleRows"]
    primary = config["primaryRoots"]
    if manifest["roots"] != ["Nyll"] or len(primary) != len(set(primary)) or not primary:
        raise ValueError("Invalid full-root/primary partition")
    for entry, expected in (("Nyll", ["Nyll.All"]), ("Nyll.All", primary)):
        if entry not in rows or pure_imports((root / rows[entry]["path"]).read_text()) != expected:
            raise ValueError("Global entry must contain exactly the audited imports: " + entry)
    graph = {name: [dep for dep, _, _ in generate_manifest.header_imports(
        (root / row["path"]).read_text()) if dep in rows] for name, row in rows.items()}
    shards, covered = {}, set()
    for entry in primary:
        if entry not in rows or not re.fullmatch(r"Nyll\.[A-Za-z0-9_]+\.All", entry):
            raise ValueError("Missing or invalid primary root: " + entry)
        closure, todo = set(), [entry]
        while todo:
            name = todo.pop()
            if name in closure:
                continue
            closure.add(name)
            todo.extend(graph[name])
        if closure & {"Nyll", "Nyll.All"}:
            raise ValueError("A library imports a global aggregate")
        shards[entry.split('.')[1]] = {"roots": [entry], "moduleRows": {
            name: rows[name] for name in sorted(closure)}}
        covered.update(closure)
    if covered | {"Nyll", "Nyll.All"} != set(rows):
        raise ValueError("Verification partition omits maintained sources")
    return shards


def select_scope(root, manifest, config, shard):
    if shard == "all":
        return manifest
    shards = partition(root, manifest, config)
    if shard not in shards:
        raise ValueError("Unknown verification shard: " + shard)
    return shards[shard]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--partition", action="store_true")
    args = parser.parse_args()
    config = generate_manifest.load_json(args.config)
    manifest, report = generate_manifest.analyze(args.root, config)
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / "source-audit.json").write_text(json.dumps(report, indent=2) + "\n")
    if not report["staticPassed"] or not report["allPhysicalSourcesMapped"]:
        raise ValueError("Physical source audit failed: " + str(report["errors"]))
    (args.output / "modules.json").write_text(json.dumps(manifest, indent=2) + "\n")
    keys = list(partition(args.root, manifest, config)) if args.partition else ["all"]
    # The matrix is derived from the exact current source, never a maintained list
    # which could silently omit a newly added library.
    plan = {"shard": keys}
    (args.output / "matrix.json").write_text(json.dumps(plan) + "\n")
    print(json.dumps(plan))


if __name__ == "__main__":
    main()
