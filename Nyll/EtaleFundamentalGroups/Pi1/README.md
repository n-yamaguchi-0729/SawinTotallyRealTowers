# pi1 adaptations in NYLL

This directory records NYLL's maintained adaptations of
[Christian Merten's pi1](https://github.com/chrisflav/pi1), pinned to
[`5c5c0171efc863ce9990171bdf46d7cb5fd582fb`](https://github.com/chrisflav/pi1/tree/5c5c0171efc863ce9990171bdf46d7cb5fd582fb).
The exact historical import commit remains unknown.

The upstream comparison contains 25 leaf modules. The original 25 NYLL files map
to 23 upstream leaves; the other two are supplied by current mathlib APIs.
Foundation ports live in `Nyll/SchemeTheory/Pi1` at depth 1. The finite étale and
field-point ports here belong to `EtaleFundamentalGroups` at depth 2. NYLL proof
completions and extensions remain separately identified at their existing owners.
These are adaptations with API and proof repairs, not pristine upstream copies. Four previously
mapped ports now use canonical mathlib directly. The current layout contains 21
adapted port files, four NYLL extensions, and 13 aggregate modules; six upstream
leaves are supplied by mathlib rather than separate local copies.

[UPSTREAM.json](UPSTREAM.json) records the complete upstream tree, source hashes,
original-to-current mappings, local additions, dependency versions and attribution
evidence. [ATTRIBUTION.md](ATTRIBUTION.md) explains the source credits, and
[LICENSE](LICENSE) reproduces the upstream Apache-2.0 license byte for byte.

The upstream pin is frozen until an explicitly reviewed refresh. NYLL uses Lean
4.35.0-rc2; upstream uses 4.30.0-rc2 with a different mathlib pin. Normal
`lake --wfail` validation is required for the maintained ports. Exact validation
results are recorded separately after the build; these provenance files make no
build-success claim. Necessary repairs must be followed by a refresh of the
registered local-source hashes. In particular, upstream's unfinished `Point.lean`
proofs must not overwrite NYLL's completed constructions.

The newly written NYLL documentation is Copyright (c) 2026 Naganori Yamaguchi,
licensed under Apache-2.0. Authors: Naganori Yamaguchi (assisted by OpenAI Codex),
<https://github.com/n-yamaguchi-0729>. Recorded pi1, mathlib and other external
source notices retain their own attribution; this credit does not apply to them
or to the unchanged upstream license.
