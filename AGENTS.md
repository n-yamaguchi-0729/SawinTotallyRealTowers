# Public library workspace instructions

This repository is a source extract of NYLL. Its primary roots are `Nyll.SawinTotallyRealTowers.All`.
Keep exactly their recursive local import closure. Do not bundle an entire dependency library to supply individual modules. Nyll/All.lean imports only the primary roots.

The publication pipeline verifies source bytes against the recorded NYLL commit. Preserve copyright, author and source notices for every retained file; README and NOTICE describe only material actually included. Record the source SHA and managed file hashes in .github/verification/publication.json.

Within the shared NYLL publication workspace, validate Lean in the canonical NYLL root and reuse its .lake/build cache; do not build this exported checkout. GitHub CI and independent consumers build from this repository root using its pinned toolchain and .lake/build. Never relocate the build cache.

Automatic updates accept only a successful libraries.yml run for the exact current NYLL main commit. They cannot roll back or replace a divergent published snapshot. Use normal pushes and rerun lean.yml after a changed extract is committed.
