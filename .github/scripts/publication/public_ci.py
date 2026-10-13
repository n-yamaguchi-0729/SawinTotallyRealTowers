#!/usr/bin/env python3
"""Generate public CI policy from an exact module export; never invoke Lean or Git.

Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0. Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The existing manifest audit and depth-frontier builder remain the shared owners.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

TEMPLATES = Path(__file__).resolve().with_name("ci_templates")
SCRIPT_REPOS = {"AnabelianGeometry", "EtaleFundamentalGroupsAndCohomology",
                "JacobianVarieties", "YamaguchiPapersFormalization"}
VERIFICATION_REPOS = {"ClassFieldTheory", "ProCGroups", "SawinTotallyRealTowers"}


def library_workflow(depths):
    """Wait for each actual import depth before the aggregate/default target."""
    text = """name: Lean

on:
  push:
    branches: [main]
  pull_request:
  workflow_dispatch:

permissions:
  contents: read

concurrency:
  group: lean-${{ github.ref }}
  cancel-in-progress: true

jobs:
"""
    previous = None
    for depth in sorted(set(depths)):
        job = f"depth{depth}"
        text += f"  {job}:\n    name: Import depth {depth}\n"
        if previous:
            text += f"    needs: {previous}\n"
        text += """    if: github.event.repository.private == false || github.event_name == 'workflow_dispatch'
    uses: ./.github/workflows/library-stage.yml
    with:
"""
        text += f"      stage: {job}\n\n"
        previous = job
    text += f"  all:\n    name: Nyll.All and Nyll\n    needs: {previous}\n"
    text += """    if: github.event.repository.private == false || github.event_name == 'workflow_dispatch'
    uses: ./.github/workflows/library-stage.yml
    with:
      stage: all
      target: +Nyll.All
"""
    return text



def desired_ci(repo, record):
    """Return relative-path -> bytes updates for one immutable export record.

    The caller owns atomic application, source byte verification and publication.
    This function only reads the supplied checkout and shared templates.
    """
    repo = Path(repo).resolve()
    name = record["repository"]
    if name not in SCRIPT_REPOS | VERIFICATION_REPOS:
        raise ValueError("Unsupported public repository: " + name)
    if not repo.is_dir():
        raise ValueError("Missing public checkout: " + str(repo))
    directory = ".github/scripts" if name in SCRIPT_REPOS else ".github/verification"
    path = directory + "/manifest-config.json"
    config = json.loads((repo / path).read_text(encoding="utf-8"))
    ordered = record["ordered_libraries"]
    primary = record["primary_roots"]
    depths = record["depths"]
    if (not ordered or len(set(ordered)) != len(ordered) or set(depths) != set(ordered)
            or not primary or len(set(primary)) != len(primary)):
        raise ValueError("Invalid export library/root policy")
    if any(not isinstance(depths[owner], int) or depths[owner] not in (1, 2, 3)
           for owner in ordered):
        raise ValueError("Unsupported depth in the export")
    if [depths[owner] for owner in ordered] != sorted(depths.values()):
        raise ValueError("Export libraries are not in depth order")
    if primary != ["Nyll." + owner + ".All" for owner in ordered
                   if "Nyll." + owner + ".All" in primary]:
        raise ValueError("Export primary roots are missing or out of canonical order")
    config.update(owners={owner: ["Nyll." + owner] for owner in ordered} |
                  {"EntryPoint": ["Nyll"]}, roots=["Nyll"],
                  orderedLibraries=ordered, primaryRoots=primary, depths=depths,
                  leanToolchain=record["lean_toolchain"],
                  mathlibRevision=record["mathlib_revision"],
                  mathlibRepository=record["mathlib_repository"])
    desired = {path: (json.dumps(config, indent=2, ensure_ascii=False) + "\n").encode()}
    for filename in ("generate_manifest.py", "build_stage.py"):
        desired[directory + "/" + filename] = (TEMPLATES / filename).read_bytes()
    if name in SCRIPT_REPOS:
        for filename in ("audit.py", "library-build.sh"):
            desired[directory + "/" + filename] = (TEMPLATES / filename).read_bytes()
        desired[".github/workflows/library-stage.yml"] = (TEMPLATES / "library-stage.yml").read_bytes()
        desired[".github/workflows/lean.yml"] = library_workflow(depths.values()).encode()
    return desired


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--record", type=Path, required=True,
                        help="JSON object for one repository from the exporter")
    parser.add_argument("--output", type=Path, required=True,
                        help="Candidate directory; never writes into the public checkout")
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    if output == repo or output.is_relative_to(repo):
        raise ValueError("Candidate output must be outside the public checkout")
    record = json.loads(args.record.read_text(encoding="utf-8"))
    desired = desired_ci(repo, record)
    output.mkdir(parents=True, exist_ok=False)
    for rel, data in desired.items():
        target = output / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    print(json.dumps({"repository": record["repository"], "files": {
        rel: hashlib.sha256(data).hexdigest() for rel, data in desired.items()},
        "buildsRun": False, "publicCheckoutModified": False}, indent=2))


if __name__ == "__main__":
    main()
