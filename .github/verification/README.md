# Verification

The [Lean workflow](../workflows/lean.yml) shares the build, declaration
inventory, complete safe-root export, pinned NanoDa, official kernel replay,
main API, and whitespace checks with CFT and ProCGroups. Run it from the
repository root. Its repository-specific inputs are:

- `manifest-config.json`: maintained source owners, import roots, and exact
  Lean and mathlib pins. It excludes the two statement checks in `tests/`
  from the library-source inventory.
- `main-declarations.json`: selected public declarations whose names, kinds,
  owner, and specified source modules must remain available.
- `source-manifest.json`: the exact SHA-pinned 1,740-module closure.
- `historical-partial-baseline.json`: seven pre-existing partial declarations
  and the exact source hashes that produced them.

The other files implement the shared procedure:

1. `generate_manifest.py` inventories every maintained physical Lean source,
   checks import reachability and records source hashes. Its general CFT source
   policy is disabled here because Sawin has seven historical partials. The
   separate pinned closure checker rejects source `sorry`, `admit`,
   `native_decide`, `axiom`, and `unsafe` declarations; the compiled inventory
   rejects new partials. For the seven historical partials it checks both the
   current whole-file SHA and the original body SHA after an exact recognized
   copyright header.
   Python regression tests exercise those inventory guards.
2. `check_source_closure.py` checks each bundled source hash, import, and exact
   closure against the pinned manifest, then compares it with the generated
   physical inventory.
3. `setup_tools.py` obtains and builds pinned `lean4export` and NanoDa revisions.
   The workflow obtains the pinned Lean toolchain and mathlib cache first.
4. `verify.py` runs the mandatory build with warnings as errors, inventories
   every declaration (including private declarations), selects and exports the
   safe declaration union, checks exact export coverage, checks it with NanoDa,
   and replays the import closure with the official Lean kernel. `Inventory.lean`,
   `ExportSelected.lean`, and `ReplaySix.lean` implement its Lean stages. The
   exact Formal Conjectures and Martinet statement files in `tests/` also compile.
5. `check_main_declarations.py` checks the selected public API against the
   audited inventory and the successful verification receipts. This checks
   declaration presence and kind; it does not compare theorem statements.
6. The workflow checks whitespace and uploads logs, manifests, and receipts
   even if a stage fails.

The runtime stages run in order: build, inventory, selection, export, coverage,
NanoDa, and kernel replay. Every stage must pass. Use a fresh output directory
for each local attempt and follow the commands in the workflow; a static source
audit alone does not verify proofs. Full verification requires a clean committed
checkout. The expanded bundle's full NanoDa pipeline has not yet been run.
The workflow keeps its artifacts for 14 days.
