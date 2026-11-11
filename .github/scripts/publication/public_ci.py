#!/usr/bin/env python3
"""Generate public CI policy from an exact module export; never invoke Lean or Git.

Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0. Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The existing manifest audit and source-frontier builder remain the shared owners.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path
from legacy_ci import legacy_workflow

TEMPLATES = Path(__file__).resolve().with_name("ci_templates")
SCRIPT_REPOS = {"AnabelianGeometry", "EtaleFundamentalGroupsAndCohomology",
                "GeneralizedJacobianVarieties", "YamaguchiPapersFormalization"}
VERIFICATION_REPOS = {"ClassFieldTheory", "ProCGroups", "SawinTotallyRealTowers"}


# Natural CFT sublibraries prevent a fresh CFT build occupying one five-hour job.
CFT_SUBLIBRARIES = [
    "Algebra", "AbstractClassFieldTheory", "LocalFieldTheory", "RamificationTheory",
    "LubinTate", "AlgebraicNumberTheory", "AlgebraicFunctionFieldTheory", "KummerTheory",
    "LocalClassFieldTheory.ClassFormation", "LocalClassFieldTheory.LubinTateApplication",
    "LocalClassFieldTheory.Finite", "LocalClassFieldTheory", "GlobalClassFieldTheory",
    "KroneckerWeber",
]


def library_stages(ordered):
    """Stable selectors: new modules in existing libraries need no workflow edits."""
    if not ordered or len(set(ordered)) != len(ordered) or any(
            not isinstance(name, str) or not re.fullmatch(r"[A-Za-z][A-Za-z0-9]*", name)
            for name in ordered):
        raise ValueError("Expected distinct canonical library names")
    stages = []
    for library in ordered:
        if library == "ClassFieldTheory":
            stages.extend("ClassFieldTheory." + suffix for suffix in CFT_SUBLIBRARIES)
        stages.append(library)
    return stages


def library_workflow(ordered):
    """One library/sublibrary per job, with a cache handoff between jobs."""
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
    for library in library_stages(ordered):
        job = "library-" + library.lower().replace(".", "-")
        text += f"  {job}:\n    name: {library}\n"
        if previous:
            text += f"    needs: {previous}\n"
        text += """    if: github.event.repository.private == false || github.event_name == 'workflow_dispatch'
    uses: ./.github/workflows/library-stage.yml
    with:
"""
        text += f"      stage: {job}\n      library: {library}\n\n"
        previous = job
    text += f"  all:\n    name: Nyll.All and Nyll\n    needs: {previous}\n"
    text += """    if: github.event.repository.private == false || github.event_name == 'workflow_dispatch'
    uses: ./.github/workflows/library-stage.yml
    with:
      stage: all
      target: +Nyll.All

  verify:
    name: NanoDa and Lean kernel replay
    needs: all
    if: github.event.repository.private == false
    uses: ./.github/workflows/proof-check.yml

  publish-cache:
    name: Publish verified Lean cache
    needs: verify
    if: github.event.repository.private == false && github.ref == 'refs/heads/main'
    permissions:
      contents: write
    uses: ./.github/workflows/cache-release.yml
    with:
      cache-kind: modern
      cache-prefix: proof-build-v4
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
    # Distributed checker wrappers are tooling, never maintained library sources.
    # This also covers the three older verification configurations on next sync.
    config["excludedPaths"] = list(dict.fromkeys(config.get("excludedPaths", []) +
                                                [".github/scripts/publication"]))
    desired = {path: (json.dumps(config, indent=2, ensure_ascii=False) + "\n").encode()}
    for filename in ("generate_manifest.py", "build_stage.py"):
        desired[directory + "/" + filename] = (TEMPLATES / filename).read_bytes()
    if name in SCRIPT_REPOS:
        for filename in ("audit.py", "library-build.sh"):
            desired[directory + "/" + filename] = (TEMPLATES / filename).read_bytes()
        desired[".github/workflows/library-stage.yml"] = (TEMPLATES / "library-stage.yml").read_bytes()
        desired[".github/workflows/proof-check.yml"] = (TEMPLATES / "proof-check.yml").read_bytes()
        desired[".github/workflows/lean.yml"] = library_workflow(ordered).encode()
    if name in VERIFICATION_REPOS:
        desired[".github/workflows/build-library.yml"] = (TEMPLATES / "build-library.yml").read_bytes()
        desired[".github/workflows/lean.yml"] = legacy_workflow(
            (repo / ".github/workflows/lean.yml").read_text(), library_stages(ordered)).encode()
    desired[".github/workflows/cache-release.yml"] = (TEMPLATES / "cache-release.yml").read_bytes()
    desired[".github/scripts/cache-export.py"] = (TEMPLATES / "cache-export.py").read_bytes()
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
