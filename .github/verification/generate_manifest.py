#!/usr/bin/env python3
"""Build-free Lake TOML source inventory. This lexical audit is not a proof checker."""
from __future__ import annotations
import argparse
from collections import Counter, deque
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tomllib

NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
SHA = re.compile(r"[0-9a-f]{40}\Z")
IMPORT = re.compile(r"^\s*(?:(?:public|meta)\s+){0,2}import(?:\s+(.*))?$")
FORBIDDEN = re.compile(r"(?<![\w'.])(?:sorry|admit|native_decide|axiom|constant)(?![\w'])")
LIMITATION = ("Static lexical/configuration checks do not establish proof safety. "
              "They do not elaborate Lean, expand macros, resolve external modules, "
              "or verify compiled proof terms. Run the private-level axiom inventory, "
              "the Lean kernel checker, and the independent checker on the same source snapshot.")
RESERVED_OWNERS = {"all-selected", "primary", "repaired", "repaired-outside-primary", ".", ".."}


def load_json(path):
    def unique(pairs):
        out = {}
        for key, value in pairs:
            if key in out:
                raise ValueError(f"Duplicate JSON key: {key}")
            out[key] = value
        return out
    return json.loads(Path(path).read_text(encoding="utf-8"), object_pairs_hook=unique)


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def valid_name(value):
    return isinstance(value, str) and bool(NAME.fullmatch(value))


def prefix_of(prefix, name):
    return name == prefix or name.startswith(prefix + ".")


def mask_noncode(text):
    """Mask nested comments, strings and escaped identifiers; preserve line offsets."""
    out = list(text)
    i, depth, string, escaped, quoted = 0, 0, False, False, False
    while i < len(text):
        ch, two = text[i], text[i:i + 2]
        if depth:
            if two == "/-":
                out[i:i + 2] = "  "; depth += 1; i += 2; continue
            if two == "-/":
                out[i:i + 2] = "  "; depth -= 1; i += 2; continue
            if ch != "\n": out[i] = " "
        elif string:
            if ch != "\n": out[i] = " "
            if escaped: escaped = False
            elif ch == "\\": escaped = True
            elif ch == '"': string = False
        elif quoted:
            if ch != "\n": out[i] = " "
            if ch == "»": quoted = False
        elif two == "--":
            end = text.find("\n", i)
            if end < 0: end = len(text)
            out[i:end] = " " * (end - i); i = end; continue
        elif two == "/-":
            out[i:i + 2] = "  "; depth = 1; i += 2; continue
        elif ch == '"':
            out[i] = " "; string = True
        elif ch == "«":
            out[i] = " "; quoted = True
        i += 1
    if depth or string or quoted:
        raise ValueError("Unterminated comment, string, or escaped identifier.")
    return "".join(out)


def source_policy(clean):
    errors = []
    if not re.search(r"^\s*set_option\s+autoImplicit\s+false\s*$", clean, re.MULTILINE):
        errors.append("Each maintained source must set autoImplicit false globally.")
    for option in re.finditer(r"(?<![\w.])set_option\s+([^\s]+)\s+([^\s]+)", clean):
        if option.groups() != ("autoImplicit", "false"):
            errors.append("Unpermitted source option: " + " ".join(option.groups()))
    if re.search(r"(?<![\w'.])(?:unsafe|partial|nolint)(?![\w'])", clean):
        errors.append("Unsafe/partial declarations and nolint suppression are forbidden.")
    return errors


def glob_matches(glob, module):
    if glob.endswith(".+"): return module.startswith(glob[:-2] + ".")
    if glob.endswith(".*"): return prefix_of(glob[:-2], module)
    return module == glob


def analyze(root, config):
    root = Path(root).resolve()
    errors, warnings = [], []
    def error(kind, message, **context):
        errors.append(dict(kind=kind, message=message, **context))
    def inside(relative):
        path = (root / relative).resolve()
        if not path.is_relative_to(root):
            raise ValueError(f"Path escapes package root: {relative}")
        return path

    owners = config["owners"]
    roots = config["roots"]
    excluded_dirs = set(config.get("excludedDirectories", [".git", ".lake"]))
    excluded_paths = [Path(p).as_posix().rstrip("/") for p in config.get("excludedPaths", [])]
    external = config.get("externalModuleRoots", ["Mathlib", "Lean", "Init", "Std", "Batteries"])
    repaired = config.get("repairedModules", [])
    if not isinstance(owners, dict) or not owners:
        raise ValueError("owners must be a nonempty object mapping labels to module-prefix arrays.")
    for label, prefixes in owners.items():
        if (not re.fullmatch(r"[A-Za-z0-9_.-]+", label) or label in RESERVED_OWNERS
                or not isinstance(prefixes, list) or not prefixes or not all(map(valid_name, prefixes))):
            raise ValueError(f"Invalid owner specification: {label}")
    for label, names in [("roots", roots), ("externalModuleRoots", external), ("repairedModules", repaired)]:
        if not isinstance(names, list) or not all(map(valid_name, names)) or len(set(names)) != len(names):
            raise ValueError(f"{label} must contain distinct simple module names.")
    if not roots: raise ValueError("roots must not be empty.")
    for part in excluded_dirs:
        if not isinstance(part, str) or not part or "/" in part or "\\" in part or part in {".", ".."}:
            raise ValueError("excludedDirectories must contain directory basenames.")
    for relative in excluded_paths: inside(relative)
    def excluded(relative):
        return any(prefix == relative or relative.startswith(prefix + "/") for prefix in excluded_paths)

    if (root / "lakefile.lean").exists():
        raise ValueError("lakefile.lean is unsupported, including packages containing both Lake formats.")
    lake_path = root / "lakefile.toml"
    lake = tomllib.loads(lake_path.read_text(encoding="utf-8"))
    lock_path = root / "lake-manifest.json"
    lock = load_json(lock_path)
    expected_lean, expected_mathlib = config["leanToolchain"], config["mathlibRevision"]
    expected_url = config.get("mathlibRepository", "https://github.com/leanprover-community/mathlib4")
    if not re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+", expected_lean):
        raise ValueError("leanToolchain must be an exact release, not stable/nightly.")
    if not isinstance(expected_mathlib, str) or not SHA.fullmatch(expected_mathlib):
        raise ValueError("mathlibRevision must be a lowercase 40-hex commit.")
    actual_lean = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    if actual_lean != expected_lean:
        error("lean-pin", "lean-toolchain differs from the configured fixed release.", actual=actual_lean)
    requirements = [p for p in lake.get("require", []) if p.get("name") == "mathlib"]
    if len(requirements) != 1:
        error("mathlib-require", "Exactly one direct mathlib requirement is required.")
    else:
        requirement = requirements[0]
        if requirement.get("rev") != expected_mathlib or not SHA.fullmatch(str(requirement.get("rev", ""))):
            error("mathlib-require-pin", "Direct mathlib rev must equal the fixed 40-hex commit.")
        git = requirement.get("git")
        url = git.get("url") if isinstance(git, dict) else git
        if "path" in requirement or (url and str(url).removesuffix(".git") != expected_url.removesuffix(".git")):
            error("mathlib-require-source", "mathlib must use the configured Git repository.")
        if not url and requirement.get("scope") != "leanprover-community":
            error("mathlib-require-source", "Unsupported mathlib source; use explicit git or community scope.")
    packages = lock.get("packages", [])
    package_names = [p.get("name") for p in packages]
    if len(package_names) != len(set(package_names)):
        error("lock-duplicate", "Duplicate package names in lake-manifest.json.")
    for package in packages:
        if package.get("type") != "git":
            error("lock-source", "Only Git lock entries are supported by this static gate.", package=package.get("name"))
        elif not SHA.fullmatch(str(package.get("rev", ""))):
            error("lock-revision", "Every resolved Git rev must be a fixed 40-hex commit.", package=package.get("name"))
    mathlibs = [p for p in packages if p.get("name") == "mathlib"]
    if len(mathlibs) != 1 or mathlibs[0].get("rev") != expected_mathlib:
        error("mathlib-lock-pin", "Resolved mathlib must equal the configured commit.")
    elif str(mathlibs[0].get("url", "")).removesuffix(".git") != expected_url.removesuffix(".git"):
        error("mathlib-lock-source", "Resolved mathlib repository differs from the configured repository.")
    # inputRev may legitimately be main/tag for inherited mathlib dependencies; resolved rev is checked.

    package_src = inside(lake.get("srcDir", "."))
    libraries = []
    for lib in lake.get("lean_lib", []):
        name = lib.get("name")
        lib_roots = lib.get("roots", [name])
        globs = lib.get("globs", lib_roots)
        if not valid_name(name) or not all(map(valid_name, lib_roots)):
            raise ValueError("Unsupported lean_lib name/roots; only simple dotted names are supported.")
        if not isinstance(globs, list) or not all(valid_name(g[:-2] if g.endswith((".+", ".*")) else g) for g in globs):
            raise ValueError(f"Unsupported glob in {name}; use a name, Name.+, or Name.*.")
        source = (package_src / lib.get("srcDir", ".")).resolve()
        if not source.is_relative_to(root): raise ValueError(f"Library source directory escapes root: {name}")
        libraries.append(dict(name=name, roots=lib_roots, globs=globs, source=source))
    if not libraries: raise ValueError("No supported lean_lib configuration found.")

    files, skipped = [], []
    for directory, dirs, names in os.walk(root, followlinks=False):
        base = Path(directory)
        kept = []
        for name in sorted(dirs):
            path = base / name; relative = path.relative_to(root).as_posix()
            if name in excluded_dirs or excluded(relative):
                skipped.append(relative)
            elif path.is_symlink():
                error("symlink", "Nonexcluded symlink directories are unsupported.", path=relative)
            else: kept.append(name)
        dirs[:] = kept
        for name in sorted(names):
            path = base / name; relative = path.relative_to(root).as_posix()
            if path.suffix != ".lean" or excluded(relative): continue
            if path.is_symlink():
                error("symlink", "Nonexcluded Lean source symlinks are unsupported.", path=relative)
            else: files.append(path)
    rows, texts, hashes = {}, {}, {}
    for path in sorted(files):
        relative = path.relative_to(root).as_posix()
        candidates = set()
        for lib in libraries:
            if not path.is_relative_to(lib["source"]): continue
            module = ".".join(path.relative_to(lib["source"]).with_suffix("").parts)
            if not valid_name(module): continue
            local = any(prefix_of(p, module) for p in lib["roots"]) or any(glob_matches(g, module) for g in lib["globs"])
            buildable = any(glob_matches(g, module) for g in lib["globs"]) or any(
                prefix_of(p, module) and any(glob_matches(g, p) for g in lib["globs"]) for p in lib["roots"])
            if local: candidates.add((module, buildable))
        modules = {candidate[0] for candidate in candidates}
        if len(modules) != 1:
            error("source-mapping", "Physical source has no unique local Lake module mapping.", path=relative, candidates=sorted(modules))
            continue
        module = next(iter(modules))
        if not any(b for m, b in candidates if m == module):
            error("not-buildable", "Maintained source is not buildable under Lake roots/globs.", path=relative, module=module)
        labels = [owner for owner, prefixes in owners.items() if any(prefix_of(p, module) for p in prefixes)]
        if len(labels) != 1:
            error("owner-mapping", "Module must have exactly one configured owner.", module=module, owners=labels)
            continue
        if module in rows:
            error("duplicate-module", "Multiple physical files map to one module.", module=module, path=relative)
            continue
        rows[module] = {"owner": labels[0], "path": relative}
        hashes[relative] = sha256(path)
        texts[module] = path.read_text(encoding="utf-8")
    if not rows: error("empty-scope", "No maintained modules were selected.")
    for owner in owners:
        if not any(row["owner"] == owner for row in rows.values()):
            error("empty-owner", "Configured owner has no maintained source.", owner=owner)

    graph = {module: set() for module in rows}
    external_imports, import_count = set(), 0
    local_roots = {prefix.split(".")[0] for prefixes in owners.values() for prefix in prefixes}
    command_words = {"set_option", "open", "namespace", "section", "noncomputable", "def", "theorem", "lemma", "variable", "universe", "attribute"}
    for module, text in texts.items():
        path = rows[module]["path"]
        try: clean = mask_noncode(text)
        except ValueError as exc:
            error("lexical-unsupported", str(exc), path=path); continue
        for finding in FORBIDDEN.finditer(clean):
            error("forbidden-source-token", finding.group(), path=path, line=clean.count("\n", 0, finding.start()) + 1)
        if config.get("enforceSourcePolicy", False):
            for message in source_policy(clean):
                error("source-policy", message, path=path)
        previous_import = False
        for line_no, line in enumerate(clean.splitlines(), 1):
            if not line.strip(): continue
            match = IMPORT.fullmatch(line)
            if not match:
                if previous_import and line[:1].isspace() and all(valid_name(n) for n in line.split()) and line.split()[0] not in command_words:
                    error("import-unsupported", "Multiline import syntax is unsupported; put all imported names on its import line.", path=path, line=line_no)
                previous_import = False
                continue
            previous_import = True
            names = (match.group(1) or "").split()
            if not names or not all(map(valid_name, names)):
                error("import-unsupported", "Malformed or unsupported import spelling.", path=path, line=line_no)
                continue
            for target in names:
                import_count += 1
                pcg = module.split(".")[0]
                if pcg in {"PCG", "ProCGroups"} and not (prefix_of(pcg, target) or prefix_of("Mathlib", target)):
                    error("pcg-import-policy", "PCG may import only itself or Mathlib.", module=module, target=target, line=line_no)
                if target in rows: graph[module].add(target)
                elif target.split(".")[0] in local_roots or not any(prefix_of(p, target) for p in external):
                    error("unresolved-local-import", "Import has no included local source or explicitly allowed external prefix.", module=module, target=target, line=line_no)
                else: external_imports.add(target)
    for module in roots + repaired:
        if module not in rows:
            error("missing-requested-module", "Requested root/subset module is absent from maintained sources.", module=module)
    reachable, todo = set(), deque(roots)
    while todo:
        module = todo.popleft()
        if module in reachable or module not in graph: continue
        reachable.add(module); todo.extend(sorted(graph[module]))
    unreachable = sorted(set(rows) - reachable)
    if unreachable:
        error("unreachable-sources", "All maintained local sources must be reachable from the explicit roots.", modules=unreachable)
    # Kahn's algorithm flags a local import cycle (and any declarations depending on it).
    incoming = {module: len(deps) for module, deps in graph.items()}
    dependents = {module: [] for module in graph}
    for module, deps in graph.items():
        for dep in deps: dependents[dep].append(module)
    ready = deque(module for module, degree in incoming.items() if degree == 0)
    while ready:
        module = ready.popleft()
        for user in dependents[module]:
            incoming[user] -= 1
            if incoming[user] == 0: ready.append(user)
    cyclic = sorted(module for module, degree in incoming.items() if degree)
    if cyclic: error("import-cycle", "Local cycle or dependence on a local cycle.", modules=cyclic)
    manifest = {"roots": roots, "moduleRows": dict(sorted(rows.items()))}
    if repaired: manifest["repairedModules"] = repaired
    report = {
        "schemaVersion": 1, "staticPassed": not errors, "proofSafetyEstablished": False,
        "limitation": LIMITATION, "supportedConfiguration": "Lake TOML; simple module names; one-line imports; Git lock entries",
        "packageRoot": str(root), "moduleCount": len(rows), "physicalMaintainedLeanFiles": len(files),
        "allPhysicalSourcesMapped": len(rows) == len(files),
        "ownerModuleCounts": dict(sorted(Counter(row["owner"] for row in rows.values()).items())),
        "importCount": import_count, "externalImports": sorted(external_imports), "externalImportsResolved": False,
        "excludedDirectories": sorted(excluded_dirs), "excludedPaths": excluded_paths,
        "skippedDirectoryRoots": skipped, "sourceSha256": dict(sorted(hashes.items())),
        "configurationSha256": {name: sha256(root / name) for name in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]},
        "fixedLean": expected_lean, "fixedMathlibRevision": expected_mathlib,
        "resolvedGitRevisions": {p.get("name"): p.get("rev") for p in packages},
        "inheritedInputRevPolicy": "Symbolic inherited inputRev is allowed; every resolved Git rev must be 40-hex.",
        "errors": errors, "warnings": warnings,
    }
    return manifest, report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True)
    parser.add_argument("--config", required=True)
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--report", required=True)
    parser.add_argument("--check-manifest")
    args = parser.parse_args(argv)
    try:
        manifest, report = analyze(args.root, load_json(args.config))
        if args.check_manifest and load_json(args.check_manifest) != manifest:
            report["errors"].append({"kind": "manifest-mismatch", "message": "Existing manifest differs from all maintained physical sources/configured roots."})
            report["staticPassed"] = False
        report["auditConfigSha256"] = sha256(args.config)
        if report["staticPassed"]:
            Path(args.manifest).write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        Path(args.report).write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(json.dumps({"staticPassed": report["staticPassed"], "moduleCount": report["moduleCount"],
                          "errorCount": len(report["errors"]), "proofSafetyEstablished": False, "limitation": LIMITATION}))
        return 0 if report["staticPassed"] else 1
    except (OSError, ValueError, TypeError, KeyError, AttributeError) as exc:
        failure = {"staticPassed": False, "proofSafetyEstablished": False, "error": str(exc), "limitation": LIMITATION}
        Path(args.report).write_text(json.dumps(failure, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(failure), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
