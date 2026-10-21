"""Coverage and fail-closed checks without starting a Lean build.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
"""
from argparse import Namespace
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
import json
import io
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

PACKAGE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE))
sys.path.insert(0, str(PACKAGE / "verification"))
import public_ci
import public7_sync
import scope
import verify


class ScopeTests(unittest.TestCase):
    def setUp(self):
        scratch = Path.cwd() / "tmp/publication-tests"
        scratch.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=scratch)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.rows = {}
        self.put("Nyll", "import Nyll.All\n")
        self.put("Nyll.All", "import Nyll.Base.All\nimport Nyll.Target.All\n")
        self.put("Nyll.Base.All", "import Nyll.Base.Result\n")
        self.put("Nyll.Base.Result", "theorem result : True := True.intro\n")
        self.put("Nyll.Target.All", "import Nyll.Base.Result\n")
        self.full = {"roots": ["Nyll"], "moduleRows": self.rows}
        self.config = {"primaryRoots": ["Nyll.Base.All", "Nyll.Target.All"]}

    def put(self, name, body):
        path = name.replace(".", "/") + ".lean"
        dest = self.root / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(body)
        self.rows[name] = {"path": path, "owner": name.split(".")[1] if "." in name else "EntryPoint"}

    def test_partition_covers_every_nonentry_module_and_exact_dependencies(self):
        shards = scope.partition(self.root, self.full, self.config)
        self.assertEqual(set(shards), {"Base", "Target"})
        self.assertEqual(set(shards["Target"]["moduleRows"]),
                         {"Nyll.Target.All", "Nyll.Base.Result"})
        self.assertEqual(set().union(*(set(s["moduleRows"]) for s in shards.values())),
                         set(self.rows) - {"Nyll", "Nyll.All"})

    def test_all_preserves_full_manifest(self):
        self.assertEqual(scope.select_scope(self.root, self.full, self.config, "all"), self.full)

    def test_unknown_shard_fails(self):
        with self.assertRaisesRegex(ValueError, "Unknown"):
            scope.select_scope(self.root, self.full, self.config, "NoSuchLibrary")

    def test_unreachable_source_cannot_be_dropped(self):
        self.put("Nyll.Base.Hidden", "theorem hidden : True := True.intro\n")
        with self.assertRaisesRegex(ValueError, "omits"):
            scope.partition(self.root, self.full, self.config)

    def test_entry_declaration_cannot_be_omitted(self):
        self.put("Nyll", "import Nyll.All\ntheorem extra : True := True.intro\n")
        with self.assertRaisesRegex(ValueError, "declarations"):
            scope.partition(self.root, self.full, self.config)

    def test_wrong_primary_list_fails(self):
        self.config["primaryRoots"] = ["Nyll.Base.All"]
        with self.assertRaisesRegex(ValueError, "exactly"):
            scope.partition(self.root, self.full, self.config)

    def test_reverse_import_to_entry_fails(self):
        self.put("Nyll.Base.Result", "import Nyll\n")
        with self.assertRaisesRegex(ValueError, "global aggregate"):
            scope.partition(self.root, self.full, self.config)

    def test_comments_do_not_hide_body_or_join_tokens(self):
        self.assertEqual(scope.pure_imports("/- outer -- text /- nested -/ -/ import A -- end\n"), ["A"])
        for text in ('import A\n"hidden"', 'import A\n«hidden»',
                     'im/-comment-/port A', 'import A\n#check True', '/- unclosed'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                scope.pure_imports(text)


class PipelineTests(unittest.TestCase):
    def setUp(self):
        scratch = Path.cwd() / "tmp/publication-tests"
        scratch.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=scratch)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        args = Namespace(package_root=self.root, manifest=self.root / "modules.json",
            config=self.root / "config.json", output=self.root / "out", shard="all",
            exporter_checkout=self.root / "exporter", nanoda_checkout=self.root / "nanoda",
            nanoda_binary=self.root / "nanoda/bin")
        self.pipeline = verify.Pipeline(args)
        self.pipeline.out.mkdir()

    def workflow_fixture(self, entry):
        directory = self.root / ".github/workflows"
        directory.mkdir(parents=True, exist_ok=True)
        for name in (entry, "library-stage.yml", "proof-check.yml"):
            (directory / name).write_text("name: CI\n")
        return directory

    def test_public_and_nyll_workflow_layouts_are_supported(self):
        for entry in ("lean.yml", "libraries.yml"):
            with self.subTest(entry=entry):
                directory = self.workflow_fixture(entry)
                paths = verify.verification_workflows(self.root)
                self.assertEqual({p.name for p in paths},
                                 {entry, "library-stage.yml", "proof-check.yml"})
                (directory / entry).unlink()

    def test_missing_entry_workflow_is_rejected(self):
        with self.assertRaisesRegex(verify.VerificationError, "entry workflow"):
            verify.verification_workflows(self.root)

    def test_ambiguous_entry_workflows_are_rejected(self):
        directory = self.workflow_fixture("libraries.yml")
        (directory / "lean.yml").write_text("name: another CI\n")
        with self.assertRaisesRegex(verify.VerificationError, "Exactly one"):
            verify.verification_workflows(self.root)

    def test_missing_reusable_workflow_is_rejected(self):
        directory = self.workflow_fixture("libraries.yml")
        (directory / "proof-check.yml").unlink()
        with self.assertRaisesRegex(verify.VerificationError, "proof-check.yml"):
            verify.verification_workflows(self.root)

    def test_reusable_workflow_change_invalidates_input_guard(self):
        directory = self.workflow_fixture("libraries.yml")
        self.pipeline.paths = verify.verification_workflows(self.root)
        self.pipeline.baseline = {str(p): verify.digest(p) for p in self.pipeline.paths}
        with patch.object(verify, "git_identity", return_value={}):
            self.pipeline.guard()
            (directory / "proof-check.yml").write_text("name: changed verification\n")
            with self.assertRaisesRegex(verify.VerificationError, "input changed"):
                self.pipeline.guard()

    def test_input_failure_is_reported_before_any_stage_starts(self):
        self.pipeline.out.rmdir()
        with patch.object(self.pipeline, "inputs", side_effect=verify.VerificationError(
                "Missing workflow")), redirect_stderr(StringIO()) as log:
            self.assertEqual(self.pipeline.execute(), 1)
        self.assertIn("Missing workflow", log.getvalue())
        receipt = json.loads((self.pipeline.out / "final.json").read_text())
        self.assertFalse(receipt["passed"])
        self.assertEqual(receipt["stages"], [])

    def test_failed_command_has_failed_receipt_and_surfaces_log(self):
        with patch.object(self.pipeline, "guard", return_value="fixed"), redirect_stdout(StringIO()) as log:
            with self.assertRaises(verify.VerificationError):
                self.pipeline.stage("failing", [sys.executable, "-c", "print('diagnostic');exit(4)"])
        receipt = json.loads((self.pipeline.out / "failing.json").read_text())
        self.assertFalse(receipt["passed"])
        self.assertEqual(receipt["exitCode"], 4)
        self.assertIn("diagnostic", log.getvalue())

    def test_export_stdout_stays_in_artifact_and_receipt_is_sealed(self):
        output = self.pipeline.out / "export.ndjson"
        with patch.object(self.pipeline, "guard", return_value="fixed"), redirect_stdout(StringIO()) as log:
            receipt = self.pipeline.stage("export", [sys.executable, "-c", "print('export data')"], output=output)
        self.assertTrue(receipt["passed"])
        self.assertEqual(output.read_text(), "export data\n")
        self.assertNotIn("export data", log.getvalue())
        self.assertEqual(self.pipeline.sealed[str(output)], verify.digest(output))

    def test_validator_failure_is_not_command_success(self):
        def fail():
            raise verify.VerificationError("missing exact coverage")
        with patch.object(self.pipeline, "guard", return_value="fixed"), redirect_stdout(StringIO()):
            with self.assertRaisesRegex(verify.VerificationError, "coverage"):
                self.pipeline.stage("coverage", validate=fail)
        self.assertFalse(json.loads((self.pipeline.out / "coverage.json").read_text())["passed"])

    def test_full_snapshot_is_rechecked_even_for_a_shard(self):
        self.pipeline.full_manifest = {"roots": ["Nyll"], "moduleRows": {"Nyll.Target.All": {}}}
        self.pipeline.manifest = self.pipeline.full_manifest
        with patch.object(verify.generate_manifest, "load_json", return_value={"enforceSourcePolicy": True}), \
             patch.object(verify.generate_manifest, "analyze", return_value=(
                 {"roots": ["Nyll"], "moduleRows": {}},
                 {"staticPassed": True, "allPhysicalSourcesMapped": True, "errors": []})):
            with self.assertRaisesRegex(verify.VerificationError, "omitted"):
                self.pipeline.check_physical_snapshot()

    def test_nanoda_must_report_completion_without_skips(self):
        self.pipeline.selectors = ["theorem1", "theorem2"]
        logfile = self.pipeline.out / "nanoda.log"
        for text in ("", "Checked 1 declarations with no errors\n",
                     "Checked 2 declarations with no errors\nskipping unknown\n"):
            logfile.write_text(text)
            with self.assertRaises(verify.VerificationError):
                self.pipeline.check_nanoda()
        logfile.write_text("Checked 2 declarations with no errors\n")
        self.assertTrue(self.pipeline.check_nanoda()["strictThreeAxioms"])

    def test_missing_replay_module_is_rejected(self):
        self.pipeline.manifest = {"roots": ["Nyll.Target.All"], "moduleRows": {"Nyll.Target.All": {}}}
        records = [{"phase": "inventory", "roots": ["Nyll.Target.All"], "loaded_modules": []},
                   {"phase": "replay", "result": "PASS", "kernel": "official Lean 4.35.0-rc2"}]
        (self.pipeline.out / "replay.log").write_text("\n".join(map(json.dumps, records)))
        with self.assertRaisesRegex(verify.VerificationError, "omitted"):
            self.pipeline.check_replay()


class WorkflowTests(unittest.TestCase):
    def test_canonical_archive_keeps_checker_code_out_of_library_import_graph(self):
        owners = [owner for group in public7_sync.TOPICS for owner in group]
        files = {"Nyll.lean": "import Nyll.All\n", "LICENSE": "license\n",
                 "lean-toolchain": "lean:test\n", "lake-manifest.json": "{}\n"}
        files["Nyll/All.lean"] = "".join("import Nyll." + o + ".All\n" for o in owners)
        files["lakefile.toml"] = "[[lean_lib]]\nname = 'Nyll'\nglobs = " + json.dumps(
            ["Nyll.All", "Nyll"] + ["Nyll." + o + ".+" for o in owners]) + "\n"
        files.update({"Nyll/" + o + "/All.lean": "import Mathlib.Init\n" for o in owners})
        tool = public7_sync.PACKAGE + "verification/Inventory.lean"
        files[tool] = "import Lean\nunsafe def main : IO Unit := pure ()\n"
        buffer = io.BytesIO()
        with tarfile.open(fileobj=buffer, mode="w") as archive:
            for name, text in files.items():
                data = text.encode()
                info = tarfile.TarInfo(name)
                info.size = len(data)
                archive.addfile(info, io.BytesIO(data))
        with patch.object(public7_sync, "SOURCE", "a" * 40), \
             patch.object(public7_sync, "git", return_value=buffer.getvalue()):
            contents, _, _, graph, _ = public7_sync.canonical()
        self.assertIn(tool, contents)
        self.assertEqual(len(graph), len(owners) + 2)
        self.assertNotIn(public7_sync.module(tool), graph)

    def test_existing_verifiers_exclude_distributed_tooling_without_changing_workflows(self):
        scratch = Path.cwd() / "tmp/publication-tests"
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=scratch) as directory:
            repo = Path(directory)
            path = repo / ".github/verification/manifest-config.json"
            path.parent.mkdir(parents=True)
            path.write_text(json.dumps({"excludedPaths": [".github/verification"]}))
            record = {"repository": "ProCGroups", "ordered_libraries": ["ProCGroups"],
                      "primary_roots": ["Nyll.ProCGroups.All"], "depths": {"ProCGroups": 1},
                      "lean_toolchain": verify.LEAN, "mathlib_revision": "a" * 40,
                      "mathlib_repository": "https://github.com/leanprover-community/mathlib4"}
            changes = public_ci.desired_ci(repo, record)
            config = json.loads(changes[".github/verification/manifest-config.json"])
            self.assertIn(".github/scripts/publication", config["excludedPaths"])
            self.assertFalse(any(path.startswith(".github/workflows/") for path in changes))

    def test_four_missing_pipelines_require_both_checkers_after_build(self):
        for depths in ([1, 2], [1, 2, 3]):
            workflow = public_ci.library_workflow(depths)
            self.assertIn("needs: all\n", workflow)
            self.assertIn("uses: ./.github/workflows/proof-check.yml", workflow)
        template = (PACKAGE / "ci_templates/proof-check.yml").read_text()
        self.assertIn("fail-fast: false", template)
        self.assertNotIn("continue-on-error", template)
        self.assertIn("--config", template)
        self.assertIn("--shard", template)
        self.assertIn("github.event.repository.private == false", template)
        self.assertIn("if: always()", template)

    def test_preserves_three_existing_verification_workflows(self):
        self.assertEqual(public_ci.VERIFICATION_REPOS,
                         {"ProCGroups", "ClassFieldTheory", "SawinTotallyRealTowers"})
        self.assertEqual(len(public_ci.SCRIPT_REPOS), 4)


if __name__ == "__main__":
    unittest.main()
