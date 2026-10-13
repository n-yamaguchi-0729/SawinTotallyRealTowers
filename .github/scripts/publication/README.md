# Public library publication

This shared owner exports each public library and exactly its recursive NYLL imports.
It also maintains matching CI, source notices and the managed file inventory. The
seven repositories receive byte-identical copies of this directory from the recorded
NYLL source commit. Source files retain their original copyright headers.

After validating the selected source at the canonical NYLL root, preview the update:

```sh
python3 -B .github/scripts/publication/public7_sync.py \
  --root /path/to/NYLL --clones /path/to/public-libraries \
  --source FULL_40_CHARACTER_COMMIT_SHA --output /path/to/work/tmp/publication-plan
```

Add `--repository ClassFieldTheory` to select one repository. Add `--apply` to write
the reviewed source/configuration changes; this command does not commit, push or build.
Each target must be clean, on `main`, with its exact configured GitHub origin and
`HEAD == origin/main`. Review the plan, commit its explicit paths, and use a normal push.
Local Lean validation always uses the canonical NYLL root and its existing `.lake/build`.

The installed `sync-nyll.yml` checks once a day around 09:00 Japan time (00:00 UTC)
and supports manual dispatch. It accepts only the exact current NYLL `main` SHA with a successful
trusted `libraries.yml` run. A published source must be an ancestor of that SHA: an
older or divergent NYLL main cannot replace a newer development snapshot. Unchanged
extracts do not create commits or advance only the recorded source SHA.

Each repository uses its own `GITHUB_TOKEN`; no extra secret is needed. A change to
`.github/workflows/` requires manual publication and is detected before applying any
files because that token cannot modify workflows. Ordinary module changes use the
stable workflow and its dynamically computed module targets.

After a changed extract is pushed, the updater dispatches that repository's `lean.yml`.
If that dispatch fails, a later check recovers it for the exact public HEAD. An existing
failed Lean run is reported by GitHub and is not repeatedly dispatched. Auto-sync never
runs Lean, bypasses branch protection, or force-pushes.

Run the isolated Python checks from the NYLL root:

```sh
python3 -B -m unittest discover -s .github/scripts/publication/tests -v
```

Tests mock GitHub writes and Git publication operations. Test scratch files stay under
`tmp/publication-tests`; `NYLL_PUBLICATION_TEST_TMP` can select another work-local folder.

Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0. Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
