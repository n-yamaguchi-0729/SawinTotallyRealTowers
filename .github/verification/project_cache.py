#!/usr/bin/env python3
"""Seal or validate only reusable project artifacts, never dependencies or proof receipts.

The matching workflow caches lib/lean and the C/bitcode outputs required by Lake.
Generated *.setup.json files are deliberately excluded: they are large compiler
input descriptions, not required outputs (Lake 4.35 Module.checkArtifactsExist).
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def payload(root):
    build = root / ".lake/build"
    result = []
    for base in (build / "lib/lean", build / "ir"):
        if not base.exists():
            continue
        if base.is_symlink() or not base.resolve().is_relative_to(build.resolve()):
            raise ValueError("Cache directory escaped the project build directory")
        for path in base.rglob("*"):
            if path.is_symlink() or not path.resolve().is_relative_to(build.resolve()):
                raise ValueError("Symlinks are forbidden in project build cache")
            if path.is_file() and (base.name == "lean" or
                    path.name.endswith((".c", ".c.hash", ".bc", ".bc.hash"))):
                result.append(path)
    return sorted(result)


def context(root):
    return {"schemaVersion": 1, "platform": platform.system(), "machine": platform.machine(),
            "configuration": {name: digest(root / name) for name in
                ("lean-toolchain", "lakefile.toml", "lake-manifest.json")}}


def runner_guard(root, metadata):
    workspace = Path(os.environ.get("GITHUB_WORKSPACE", "/nonexistent")).resolve()
    temporary = Path(os.environ.get("RUNNER_TEMP", "/nonexistent")).resolve()
    if os.environ.get("GITHUB_ACTIONS") != "true" or workspace != root or \
            not metadata.resolve().is_relative_to(temporary) or temporary == Path("/"):
        raise ValueError("Cache mutation is restricted to the current GitHub Actions runner")
    build = root / ".lake/build"
    if build.is_symlink() or not build.resolve().is_relative_to(root):
        raise ValueError("Project build directory escaped the runner workspace")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("restore", "seal", "measure"))
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--metadata", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    files = payload(root)
    receipt = {"mode": args.mode, "fileCount": len(files), "cacheable": False}
    if args.mode == "restore":
        runner_guard(root, args.metadata)
        valid, reason = False, "cache miss"
        if args.metadata.is_file():
            try:
                recorded = json.loads(args.metadata.read_text())
                actual = {str(path.relative_to(root)): digest(path) for path in files}
                valid = recorded["context"] == context(root) and recorded["files"] == actual
                reason = "integrity verified" if valid else "cache content/configuration mismatch"
            except (OSError, ValueError, KeyError, TypeError) as error:
                reason = "invalid cache metadata: " + str(error)
        if not valid:
            # Remove only restored project payload files, never source or .lake/packages.
            for path in files:
                path.unlink()
            if args.metadata.is_file():
                args.metadata.unlink()
        receipt.update(restored=valid, reason=reason,
                       note="Lake rehash/build and every proof audit still run after any cache hit.")
    else:
        size = sum(path.stat().st_size for path in files)
        free = shutil.disk_usage(root).free
        # Reserve more than an uncompressed tar plus metadata and two GiB of headroom.
        required = size + 2 * 1024 ** 3 + len(files) * 1024
        receipt.update(payloadBytes=size, freeBytes=free, requiredFreeBytes=required,
                       cacheable=bool(files) and free >= required)
        if args.mode == "seal":
            runner_guard(root, args.metadata)
            args.metadata.write_text(json.dumps({"context": context(root),
                "files": {str(path.relative_to(root)): digest(path) for path in files}},
                sort_keys=True) + "\n")
            if not receipt["cacheable"]:
                print("::warning::Project cache cannot be saved: no payload or insufficient archive space")
            if os.environ.get("GITHUB_OUTPUT"):
                with open(os.environ["GITHUB_OUTPUT"], "a") as output:
                    output.write("cacheable=" + str(receipt["cacheable"]).lower() + "\n")
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt))


if __name__ == "__main__":
    main()
