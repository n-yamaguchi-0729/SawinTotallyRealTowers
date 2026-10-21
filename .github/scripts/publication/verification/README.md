# Proof verification

The common procedure audits every maintained module and every compiled declaration,
including private declarations. All safe declarations, together with their transitive
dependencies, are exported to the pinned NanoDa checker. The official Lean kernel
also replays the imported environment at trust level zero. The only allowed axioms
are `propext`, `Classical.choice`, and `Quot.sound`; a source, coverage, axiom, checker,
or replay failure fails CI. There is no option to skip a verification stage.

The existing Pro-C Groups, Class Field Theory, and Sawin pipelines remain in place.
The other four standalone libraries use `proof-check.yml` after their depth builds
and aggregate build. The same workflow verifies NYLL by its current primary library
roots. Its plan rejects missing modules and checks that `Nyll.lean` and `Nyll/All.lean`
contain only the exact aggregate imports. Those two declaration-free entry files
are built by the preceding aggregate job; the union of the checker scopes covers
every remaining module. Each shard also audits and binds the entire physical source
tree and configuration, so dividing the work cannot silently exclude a source file.

`Inventory.lean`, `ExportSelected.lean`, and `ReplayKernel.lean` retain the existing
CFT checker wrappers unchanged. `setup_tools.py` pins the exporter and NanoDa Git
commits. `verify.py` binds sources, tool binaries, and intermediate evidence by hash;
it runs a normal incremental warning-free build before checking the proof artifacts.
Build cache hits never replace declaration checks, NanoDa, or kernel replay. The
workflow restores the same cache paths and keys as the preceding build jobs.

Every stage records its result and duration. CI displays the active stage once a
minute, and uploads logs and receipts on failure as well as success. Success applies
only to the recorded source commit and completed checks. The official replay uses
the Lean kernel; NanoDa is a separate implementation. Unsafe and partial executable
declarations are inventoried but are not safe proof roots; the strict source and
transitive-axiom checks remain mandatory. No extra mathematical assumptions or
Sawin-specific historical exceptions are introduced by this common pipeline.

Local NYLL validation must use the designated canonical Lake root and existing build
guards. Public export checkouts are not local build roots.
