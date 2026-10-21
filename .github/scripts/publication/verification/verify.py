#!/usr/bin/env python3
"""Mandatory serial build → inventory → export → nanoda → official kernel replay.

No skip-stage or relaxed-axiom option is provided.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci_templates"))
import generate_manifest
from scope import select_scope

LEAN = "leanprover/lean4:v4.35.0-rc2"
LEAN_COMMIT = "11acb17ec6b07a8f9e9173e6845197929540936b"
EXPORT_COMMIT = "6cea97789dc088ea47fcea15692db85685aedac5"
NANODA_COMMIT = "4c544ed4099c8227f07d5de77ad1e69fb0740a27"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ALLOWED_PARTS = {(("str", "propext"),), (("str", "Classical"), ("str", "choice")),
                 (("str", "Quot"), ("str", "sound"))}
WRAPPERS = ("Inventory.lean", "ExportSelected.lean", "ReplayKernel.lean")
INVENTORY_FILES = ("summary.json", "declarations.jsonl",
                   "exceptional-declarations.jsonl", "modules.json")
HERE = Path(__file__).resolve().parent


class VerificationError(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def utc():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def write_json(path, value):
    # Never leave a partly written PASS receipt.
    temp = path.with_name(path.name + ".tmp")
    temp.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")
    temp.replace(path)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=unique_object)


def contained_file(base, relative):
    require(isinstance(relative, str) and not Path(relative).is_absolute(),
            "Manifest source paths must be relative")
    path = (base / relative).resolve()
    require(path.is_relative_to(base) and path.is_file(),
            "Missing source or source outside package: " + relative)
    return path


def verification_workflows(root):
    """Bind the actual entry workflow and both local reusable workflows."""
    directory = root / ".github/workflows"
    entries = [directory / name for name in ("lean.yml", "libraries.yml")
               if (directory / name).is_file()]
    require(len(entries) == 1, "Exactly one Lean entry workflow is required")
    paths = entries + [directory / "library-stage.yml", directory / "proof-check.yml"]
    return [contained_file(root, str(path.relative_to(root))) for path in paths]


def physical_manifest(root, manifest_path):
    """Bind every manifest path; discovery of omitted maintained files is external."""
    manifest = read_json(manifest_path)
    roots, rows = manifest.get("roots"), manifest.get("moduleRows")
    require(isinstance(roots, list) and roots and all(
        isinstance(n, str) and n and not n.startswith("-") for n in roots), "Invalid roots")
    require(len(roots) == len(set(roots)), "Duplicate roots")
    require(isinstance(rows, dict) and rows, "Missing moduleRows")
    require(set(roots) <= set(rows), "Every root needs a physical moduleRows entry")
    repairs = manifest.get("repairedModules", [])
    require(isinstance(repairs, list) and all(isinstance(n, str) for n in repairs),
            "Invalid repairedModules")
    require(len(repairs) == len(set(repairs)) and set(repairs) <= set(rows),
            "Every repaired module needs a physical moduleRows entry")
    paths = []
    for name, row in rows.items():
        require(isinstance(name, str) and name and isinstance(row, dict), "Invalid module row")
        require(isinstance(row.get("owner"), str) and row["owner"], "Missing owner")
        relative = row.get("path")
        require(isinstance(relative, str) and relative.endswith(".lean"), "Missing Lean source path")
        paths.append(contained_file(root, relative))
    require(len(paths) == len(set(paths)), "Physical source appears under multiple module names")
    lakefiles = [root / name for name in ("lakefile.toml", "lakefile.lean")
                 if (root / name).is_file()]
    require(len(lakefiles) == 1, "Exactly one Lakefile is required")
    for name in ("lean-toolchain", "lake-manifest.json"):
        require((root / name).is_file(), "Missing " + name)
        paths.append(root / name)
    require((root / "lean-toolchain").read_text().strip() == LEAN, "Lean toolchain pin mismatch")
    paths.extend(lakefiles)
    paths.append(manifest_path)
    return manifest, paths


def git_identity(checkout, commit):
    require(checkout.is_dir(), "Missing tool checkout: " + str(checkout))
    def git(*args):
        return subprocess.check_output(["git", "-C", str(checkout), *args], text=True).strip()
    require(Path(git("rev-parse", "--show-toplevel")).resolve() == checkout,
            "Tool path is not its Git checkout root")
    require(git("rev-parse", "HEAD") == commit, "Tool commit mismatch: " + str(checkout))
    require(not git("status", "--porcelain", "--untracked-files=all"),
            "Tool checkout is dirty: " + str(checkout))
    return {"checkout": str(checkout), "commit": commit, "clean": True}


def name_parts(parts):
    require(isinstance(parts, list) and parts, "Missing structural name")
    result = []
    for part in parts:
        require(isinstance(part, dict) and len(part) == 1, "Invalid name component")
        kind, value = next(iter(part.items()))
        require((kind == "str" and isinstance(value, str)) or
                (kind == "num" and type(value) is int and value >= 0), "Invalid name component type")
        result.append((kind, value))
    return tuple(result)


def export_coverage(exported, inventory, selectors):
    """Same structural-name coverage core as the reviewed preflight runner."""
    names, declarations, axioms, metadata = {0: ()}, {}, set(), None
    lines = 0
    def declare(index, kind):
        name = names[index]
        require(name not in declarations, "Duplicate exported declaration")
        declarations[name] = kind
        if kind == "axiom":
            axioms.add(name)
    with exported.open() as stream:
        for lines, line in enumerate(stream, 1):
            obj = json.loads(line, object_pairs_hook=unique_object)
            if "meta" in obj:
                require(metadata is None, "Duplicate export metadata")
                metadata = obj["meta"]
            if "in" in obj:
                index = obj["in"]
                require(index not in names, "Duplicate export name index")
                require(("str" in obj) != ("num" in obj), "Invalid export name record")
                if "str" in obj:
                    part = obj["str"]
                    suffix = name_parts([{"str": part["str"]}])[0]
                else:
                    part = obj["num"]
                    suffix = name_parts([{"num": part["i"]}])[0]
                names[index] = names[part["pre"]] + (suffix,)
            for kind in ("axiom", "def", "opaque", "thm", "quot"):
                if kind in obj:
                    declare(obj[kind]["name"], kind)
            if "inductive" in obj:
                for kind in ("types", "ctors", "recs"):
                    for declaration in obj["inductive"][kind]:
                        declare(declaration["name"], kind)
    require(metadata is not None and lines > 0, "Missing export metadata")
    selected = {name_parts(inventory[s]["nameParts"]) for s in selectors}
    require(len(selected) == len(selectors), "Selector spelling/structural collision")
    missing = sorted(s for s in selectors if name_parts(inventory[s]["nameParts"]) not in declarations)
    return {"selectedDeclarationCount": len(selected), "exportedDeclarationCount": len(declarations),
            "allSelectedPresent": not missing, "missingSelectedDeclarations": missing,
            "axiomNameParts": sorted(axioms), "unexpectedAxiomNameParts": sorted(axioms - ALLOWED_PARTS),
            "metadata": metadata, "lines": lines}


class Pipeline:
    def __init__(self, args):
        self.args = args
        self.root = args.package_root.resolve()
        self.manifest_path = args.manifest.resolve()
        self.config_path = args.config.resolve()
        self.out = args.output.resolve()
        self.exporter = args.exporter_checkout.resolve()
        self.nanoda_checkout = args.nanoda_checkout.resolve()
        self.nanoda = args.nanoda_binary.resolve()
        self.environment = dict(os.environ, LEAN_NUM_THREADS="1")
        self.environment.pop("LEAN_PATH", None)
        self.environment.pop("LEAN_SYSROOT", None)
        self.paths, self.baseline, self.sealed, self.stages = [], {}, {}, []
        self.provenance = {}

    def capture(self, command):
        return subprocess.check_output(command, cwd=self.root,
                                       env=self.environment, text=True).strip()

    def inputs(self):
        require(self.root.is_dir(), "Missing package root")
        require(self.manifest_path.is_file(), "Missing module manifest")
        self.full_manifest, self.paths = physical_manifest(self.root, self.manifest_path)
        self.config = generate_manifest.load_json(self.config_path)
        self.manifest = select_scope(self.root, self.full_manifest, self.config, self.args.shard)
        self.scope_path = self.out / "scope.json"
        write_json(self.scope_path, self.manifest)
        self.paths.extend([self.config_path, self.scope_path,
                          Path(generate_manifest.__file__).resolve()])
        self.check_physical_snapshot()
        self.paths += [p for p in HERE.rglob("*")
                       if p.is_file() and "__pycache__" not in p.parts]
        self.paths.extend(verification_workflows(self.root))
        for name in WRAPPERS:
            path = HERE / name
            require(path.is_file(), "Missing audit wrapper: " + name)
            self.paths.append(path)
        self.paths.append(Path(__file__).resolve())
        require(self.nanoda.is_file() and os.access(self.nanoda, os.X_OK), "Missing executable nanoda")
        require(self.nanoda.is_relative_to(self.nanoda_checkout),
                "nanoda binary must be built inside the pinned checkout")
        self.provenance["exporter"] = git_identity(self.exporter, EXPORT_COMMIT)
        self.provenance["nanoda"] = git_identity(self.nanoda_checkout, NANODA_COMMIT)
        core_dir = self.exporter / ".lake/build/lib/lean"
        core = core_dir / "Export.olean"
        require(core.is_file(), "Build the pinned exporter Export module first")
        require((self.exporter / "Export.lean").is_file(), "Missing exporter source")
        self.export_core_dir = core_dir
        self.paths += [self.nanoda, self.exporter / "Export.lean", self.exporter / "lean-toolchain"]
        # Bind all built exporter olean parts, including server/private companions.
        self.paths += sorted(core_dir.rglob("*.olean*"))
        version = self.capture(["lake", "env", "lean", "--version"])
        require("version 4.35.0-rc2" in version and LEAN_COMMIT in version, "Active Lean version mismatch")
        prefix = Path(self.capture(["lake", "env", "lean", "--print-prefix"])).resolve()
        self.lean = prefix / "bin/lean"
        require(self.lean.is_file(), "Missing active Lean executable")
        self.paths += [self.lean, prefix / "src/lean/Lean/Replay.lean"]
        self.paths += sorted((prefix / "lib/lean/Lean").glob("Replay.olean*"))
        self.paths += sorted((prefix / "lib/lean").glob("libleanshared*.so"))
        lake = shutil.which("lake")
        require(lake is not None, "Missing Lake executable")
        self.paths.append(Path(lake).resolve())
        missing = [str(p) for p in self.paths if not p.is_file()]
        require(not missing, "Missing pinned input artifacts: " + ", ".join(missing))
        self.paths = sorted(set(self.paths))
        self.baseline = {str(p): digest(p) for p in self.paths}
        self.provenance.update(leanVersion=version, leanExecutable=str(self.lean),
                               sourceCommit=self.capture(["git", "rev-parse", "HEAD"]),
                               shard=self.args.shard, fullModuleManifest=self.full_manifest,
                               fileSha256=self.baseline, moduleManifest=self.manifest)
        write_json(self.out / "inputs.json", self.provenance)
        self.sealed[str(self.out / "inputs.json")] = digest(self.out / "inputs.json")
        self.inventory, self.selectors, self.coverage = {}, [], {}

    def check_physical_snapshot(self):
        config = generate_manifest.load_json(self.config_path)
        require(config.get("enforceSourcePolicy") is True, "Source policy must be enabled")
        manifest, report = generate_manifest.analyze(self.root, config)
        require(report["staticPassed"] and report["allPhysicalSourcesMapped"],
                "Current physical source inventory/policy failed: " + str(report["errors"]))
        require(manifest == self.full_manifest, "Physical source manifest changed or omitted a module")
        require(select_scope(self.root, manifest, config, self.args.shard) == self.manifest,
                "Verification scope changed or omitted a module")

    def guard(self):
        git_identity(self.exporter, EXPORT_COMMIT)
        git_identity(self.nanoda_checkout, NANODA_COMMIT)
        current = {str(p): digest(p) for p in self.paths}
        require(current == self.baseline, "Source/config/tool input changed")
        require(all(Path(p).is_file() and digest(p) == sha for p, sha in self.sealed.items()),
                "A previous stage artifact changed")
        return hashlib.sha256(json.dumps(current, sort_keys=True).encode()).hexdigest()

    def stage(self, name, command=None, *, output=None, validate=None, artifacts=(), environment=None):
        start = time.monotonic()
        print(f"::group::{name} ({self.args.shard})", flush=True)
        print(f"{utc()} starting {name}", flush=True)
        receipt = {"stage": name, "passed": False, "status": "started", "startedUtc": utc(),
                   "command": command, "exitCode": None}
        path = self.out / (name + ".json")
        write_json(path, receipt)
        log = self.out / (name + ".log")
        try:
            receipt["inputsBeforeSha256"] = self.guard()
            settings = dict(self.environment, **(environment or {}))
            receipt["environment"] = {"LEAN_NUM_THREADS": "1"}
            if environment:
                receipt["environment"].update(environment)
            with log.open("wb") as stderr:
                if command is not None:
                    if output is None:
                        proc = subprocess.Popen(command, cwd=self.root, env=settings,
                                                stdout=stderr, stderr=subprocess.STDOUT)
                    else:
                        with output.open("wb") as stdout:
                            proc = subprocess.Popen(command, cwd=self.root, env=settings,
                                                    stdout=stdout, stderr=stderr)
                    # Keep machine-readable export stdout in its file. Announce the
                    # active stage every minute even when a checker is silent.
                    while True:
                        try:
                            proc.wait(timeout=60)
                            break
                        except subprocess.TimeoutExpired:
                            print(f"{utc()} {name}: running, {int(time.monotonic()-start)}s, "
                                  f"log {log.stat().st_size} bytes", flush=True)
                    receipt["exitCode"] = proc.returncode
                    require(proc.returncode == 0, name + " process failed")
                else:
                    receipt["exitCode"] = 0
            if validate is not None:
                receipt["validation"] = validate()
            receipt["inputsAfterSha256"] = self.guard()
            generated = [log, *artifacts] + ([output] if output else [])
            require(all(p.is_file() for p in generated), "Missing stage output: " + name)
            receipt["artifactSha256"] = {str(p): digest(p) for p in generated}
            self.sealed.update(receipt["artifactSha256"])
            receipt.update(passed=True, status="finished")
        except BaseException as error:
            receipt.update(error=str(error), status="failed")
            if receipt["exitCode"] is None:
                receipt["exitCode"] = 1
            raise
        finally:
            receipt.update(completedUtc=utc(), elapsedSeconds=round(time.monotonic() - start, 3))
            write_json(path, receipt)
            self.stages.append({"stage": name, "passed": receipt["passed"], "receipt": str(path),
                                "sha256": digest(path)})
            self.sealed[str(path)] = digest(path)
            print(f"{utc()} {name}: {receipt['status']} ({receipt['elapsedSeconds']}s)", flush=True)
            if not receipt["passed"] and log.exists():
                with log.open("rb") as stream:
                    stream.seek(max(0, log.stat().st_size - 8000))
                    print(stream.read().decode("utf-8", errors="replace"), flush=True)
            print("::endgroup::", flush=True)
        return receipt

    def check_inventory(self):
        summary = read_json(self.out / "summary.json")
        require(summary["auditPassed"] and summary["moduleCoverageExact"], "Inventory audit failed")
        require(not summary["missingRequestedModules"] and not summary["missingRootModules"],
                "Inventory omitted a requested module")
        require(summary["importRoots"] == self.manifest["roots"], "Inventory root mismatch")
        require(summary["primaryModuleCount"] == len(self.manifest["moduleRows"]),
                "Inventory module cardinality mismatch")
        rows = {}
        with (self.out / "declarations.jsonl").open() as stream:
            for line in stream:
                row = json.loads(line, object_pairs_hook=unique_object)
                require(row["name"] not in rows, "Duplicate inventory declaration")
                origin = self.manifest["moduleRows"].get(row["originModule"])
                require(origin is not None and row["primaryOwner"] == origin["owner"],
                        "Inventory origin/owner outside physical manifest")
                require(row["nameToStringRoundTrip"], "Inventory name roundtrip failed")
                require(not row["nonstandardAxioms"] and not row["hasTransitiveSorry"]
                        and not row["typeHasSorry"] and not row["valueHasSorry"], "Unsafe axiom/sorry finding")
                require(row["isSafeKernelRoot"] == (not row["isUnsafe"] and not row["isPartial"]),
                        "Inconsistent inventory safety classification")
                name_parts(row["nameParts"])
                rows[row["name"]] = row
        require(rows and len(rows) == summary["allSelected"]["declarations"], "Empty/incomplete inventory")
        self.inventory, self.summary = rows, summary
        return {"declarations": len(rows), "moduleCoverageExact": True}

    def select_union(self):
        self.selectors = sorted(n for n, row in self.inventory.items() if row["isSafeKernelRoot"])
        require(self.selectors and len(self.selectors) == self.summary["allSelected"]["safeDeclarations"],
                "Safe selector union count mismatch")
        counts = Counter(self.inventory[n]["primaryOwner"] for n in self.selectors)
        require(set(self.summary["owners"]) == {row["owner"] for row in self.manifest["moduleRows"].values()},
                "Owner coverage mismatch")
        for owner, data in self.summary["owners"].items():
            require(counts[owner] == data["statistics"]["safeDeclarations"], "Owner safe coverage mismatch")
        original = (self.out / "selectors/all-selected.safe.txt").read_text().splitlines()
        require(len(original) == len(set(original)) and set(original) == set(self.selectors),
                "Inventory selector artifact does not equal complete safe union")
        self.selector_path = self.out / "safe-union.txt"
        self.selector_path.write_text("\n".join(self.selectors) + "\n")
        return {"safeRootCount": len(self.selectors), "ownerCounts": dict(counts),
                "excludedUnsafe": sum(row["isUnsafe"] for row in self.inventory.values()),
                "excludedPartial": sum(row["isPartial"] for row in self.inventory.values())}

    def check_export(self):
        self.coverage = export_coverage(self.exported, self.inventory, self.selectors)
        write_json(self.out / "coverage-report.json", self.coverage)
        require(self.coverage["allSelectedPresent"], "Export omitted selected declarations")
        require(not self.coverage["unexpectedAxiomNameParts"], "Export has unpermitted structural axiom")
        lean = self.coverage["metadata"]["lean"]
        require(lean["version"] == "4.35.0-rc2" and lean["githash"] == LEAN_COMMIT, "Exporter version mismatch")
        return {"completeSafeUnion": True, "selectedRootCount": len(self.selectors)}

    def check_nanoda(self):
        text = (self.out / "nanoda.log").read_text()
        counts = re.findall(r"^Checked ([0-9]+) declarations with no errors\.?$", text, re.MULTILINE)
        require(len(counts) == 1 and int(counts[0]) >= len(self.selectors), "Missing exact nanoda completion")
        require("skipping" not in text.lower(), "nanoda skipped declarations")
        return {"checkedDeclarationsIncludingDependencies": int(counts[0]), "strictThreeAxioms": True}

    def check_replay(self):
        records = []
        with (self.out / "replay.log").open() as stream:
            for line in stream:
                if line.startswith("{"):
                    records.append(json.loads(line))
        completed = [r for r in records if r.get("phase") == "replay"]
        imports = [r for r in records if r.get("phase") == "inventory"]
        require(len(completed) == len(imports) == 1 and completed[0].get("result") == "PASS",
                "Missing official kernel replay completion")
        require(completed[0].get("kernel") == "official Lean 4.35.0-rc2", "Replay kernel identity mismatch")
        require(imports[0]["roots"] == self.manifest["roots"], "Replay root mismatch")
        require(set(self.manifest["moduleRows"]) <= set(imports[0]["loaded_modules"]),
                "Replay omitted physical manifest modules")
        return {"officialKernelReplay": "PASS", "axiomPolicyEnforcedBySeparateInventory": True,
                "unsafeSkippedInImportClosure": imports[0]["unsafe_skipped_count"],
                "partialSkippedInImportClosure": imports[0]["partial_skipped_count"]}

    def execute(self):
        # A fresh output directory prevents old successful evidence from hiding a failed retry.
        require(not self.out.exists(), "Output directory already exists; choose a fresh run directory")
        self.out.mkdir(parents=True)
        start = time.monotonic()
        final = {"passed": False, "status": "started", "startedUtc": utc(), "exitCode": None}
        write_json(self.out / "final.json", final)
        code = 1
        try:
            self.inputs()
            roots = self.manifest["roots"]
            self.stage("build", ["lake", "--no-ansi", "--rehash", "--wfail", "build", *roots])
            self.stage("inventory", ["lake", "env", str(self.lean), "-j1", "-DautoImplicit=false", "--run",
                       str(HERE / "Inventory.lean"), str(self.scope_path), str(self.out)],
                       validate=self.check_inventory,
                       artifacts=[self.out / n for n in INVENTORY_FILES])
            self.stage("selection", validate=self.select_union,
                       artifacts=[self.out / "safe-union.txt"])
            search = self.capture(["lake", "env", "printenv", "LEAN_PATH"])
            self.exported = self.out / "selected.ndjson"
            export_env = {"LEAN_PATH": search + os.pathsep + str(self.export_core_dir)}
            self.stage("export", [str(self.lean), "-j1", "-DautoImplicit=false", "--run", str(HERE / "ExportSelected.lean"),
                       str(self.selector_path), *roots], output=self.exported, environment=export_env)
            self.stage("coverage", validate=self.check_export, artifacts=[self.out / "coverage-report.json"])
            config = {"export_file_path": str(self.exported), "use_stdin": False,
                      "permitted_axioms": sorted(ALLOWED), "unpermitted_axiom_hard_error": True,
                      "unsafe_permit_all_axioms": False, "num_threads": 1,
                      "nat_extension": True, "string_extension": True, "pp_declars": [],
                      "unknown_pp_declar_hard_error": True, "print_success_message": True,
                      "print_axioms": True, "pp_to_stdout": True}
            config_path = self.out / "nanoda-config.json"
            write_json(config_path, config)
            self.sealed[str(config_path)] = digest(config_path)
            self.stage("nanoda", [str(self.nanoda), str(config_path)], validate=self.check_nanoda)
            self.stage("replay", ["lake", "env", str(self.lean), "-j1", "-DautoImplicit=false", "--run",
                       str(HERE / "ReplayKernel.lean"), *roots], validate=self.check_replay)
            self.guard()
            self.check_physical_snapshot()
            require([r["stage"] for r in self.stages] ==
                    ["build", "inventory", "selection", "export", "coverage", "nanoda", "replay"]
                    and all(r["passed"] for r in self.stages), "Missing mandatory successful stage")
            final.update(passed=True, status="finished", inputsSha256=digest(self.out / "inputs.json"),
                         safeSelectedDeclarations=len(self.selectors))
            code = 0
        except BaseException as error:
            final.update(status="failed", error=str(error))
            print("Verification failed: " + str(error), file=sys.stderr, flush=True)
        finally:
            final.update(completedUtc=utc(), elapsedSeconds=round(time.monotonic() - start, 3),
                         exitCode=code, stages=self.stages,
                         note="Official replay is same-kernel and skips unsafe/partial; nanoda and strict axiom inventory are separate gates.")
            write_json(self.out / "final.json", final)
        return code


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ("package-root", "manifest", "config", "output", "exporter-checkout", "nanoda-checkout", "nanoda-binary"):
        parser.add_argument("--" + flag, type=Path, required=True)
    parser.add_argument("--shard", default="all")
    args = parser.parse_args(argv)
    try:
        return Pipeline(args).execute()
    except (VerificationError, OSError) as error:
        print("Verification did not start: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
