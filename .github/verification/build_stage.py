#!/usr/bin/env python3
"""Build one actual import-depth frontier; retain completed outputs on failure."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import threading
import time

import generate_manifest

HERE = Path(__file__).resolve().parent


def plan(root, manifest, depth, depths):
    depths = dict(depths, EntryPoint=max(depths.values()) + 1)
    rows = manifest["moduleRows"]
    graph = {}
    for name, row in rows.items():
        owner = row["owner"]
        if owner not in depths:
            raise ValueError("Unassigned public library depth: " + owner)
        source = root / row["path"]
        if not source.resolve().is_relative_to(root):
            raise ValueError("Source outside the package")
        graph[name] = {target for target, _, _ in generate_manifest.header_imports(
            source.read_text(encoding="utf-8")) if target in rows}
        for target in graph[name]:
            if depths[rows[target]["owner"]] > depths[owner]:
                raise ValueError("Reverse-depth import: " + name + " -> " + target)
    selected = {name for name, row in rows.items() if depths[row["owner"]] == depth}
    if not selected:
        raise ValueError("This package has no modules at the requested depth")
    imported = {target for name in selected for target in graph[name] if target in selected}
    frontier = sorted(selected - imported)
    seen, pending = set(), list(frontier)
    while pending:
        name = pending.pop()
        if name not in seen:
            seen.add(name)
            pending.extend(graph[name])
    if not selected <= seen:
        raise ValueError("Depth frontier omits modules (possibly a local import cycle)")
    return frontier, len(selected)


def snapshot(root, manifest):
    paths = [row["path"] for row in manifest["moduleRows"].values()]
    paths += ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]
    return {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=HERE.parents[1])
    parser.add_argument("--depth", type=int, choices=(1, 2, 3), required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--plan-only", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    config = generate_manifest.load_json(HERE / "manifest-config.json")
    manifest, audit = generate_manifest.analyze(root, config)
    if not audit["staticPassed"]:
        raise ValueError("Physical source audit failed: " + str(audit["errors"]))
    frontier, count = plan(root, manifest, args.depth, config["depths"])
    command = ["lake", "--no-ansi", "--rehash", "--wfail", "build",
               *("+" + name for name in frontier)]
    args.output.mkdir(parents=True, exist_ok=False)
    before = snapshot(root, manifest)
    receipt = {"depth": args.depth, "moduleCount": count, "frontier": frontier,
               "command": command, "sourceConfigSHA256": before, "passed": False,
               "startedUTC": datetime.now(timezone.utc).isoformat(), "planOnly": args.plan_only}
    code, start = 1, time.monotonic()
    try:
        if args.plan_only:
            code = 0
        else:
            environment = dict(os.environ, LEAN_NUM_THREADS="1")
            environment.pop("LEAN_PATH", None)
            environment.pop("LEAN_SYSROOT", None)
            with (args.output / "build.log").open("wb") as log:
                process = subprocess.Popen(command, cwd=root, env=environment,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
                def stream():
                    for line in iter(process.stdout.readline, b""):
                        log.write(line)
                        log.flush()
                        print(line.decode(errors="replace"), end="", flush=True)
                worker = threading.Thread(target=stream)
                worker.start()
                try:
                    code = process.wait(timeout=300 * 60)
                except subprocess.TimeoutExpired:
                    receipt["timeoutSeconds"] = 300 * 60
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=30)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                    code = 124
                finally:
                    worker.join()
        receipt["sourceConfigUnchanged"] = snapshot(root, manifest) == before
        receipt["passed"] = code == 0 and receipt["sourceConfigUnchanged"] and not args.plan_only
        if not receipt["sourceConfigUnchanged"]:
            code = 1
    finally:
        receipt.update(exitCode=code, elapsedSeconds=round(time.monotonic() - start, 3))
        (args.output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(json.dumps({k: receipt[k] for k in
              ("depth", "moduleCount", "passed", "planOnly", "exitCode", "elapsedSeconds")}))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
