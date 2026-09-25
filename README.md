# Sawin’s totally real tower in Lean 4

There is one infinite set of primes congruent to 1 modulo 4 that splits completely in totally real number fields of arbitrarily large degree, with root discriminant at most **255255**.

```lean
import SawinTotallyRealTowers.SawinTotallyRealTower

#check ClassFieldTower.Sawin.sawin_totally_real_tower
```

The [main theorem](Lean4/SawinTotallyRealTowers/SawinTotallyRealTower.lean) matches the [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/8323e878b83fcd7f4a448256069352a265460d75/FormalConjectures/ErdosProblems/90.lean#L193). [The API check](tests/Statement.lean) repeats that exact target.

## Build

Lean **4.33.0**, Mathlib **6f1ef4e5dd604a435bddba4747b13970cd65d2a1**. Mathlib is the only direct external Git dependency; its dependencies are pinned in `lake-manifest.json`.

```sh
lake exe cache get
lake --wfail build
lake env lean --error=warning tests/Statement.lean
```

This repository bundles exactly the **1,600 local modules** reachable from the main theorem’s imports: the needed parts of CFT, PCG, GC, VFT, and Sawin. It is minimal at the file/import level for these unchanged sources; no `All` aggregates or unrelated modules are included. [Source provenance and hashes](verification/source-manifest.json) record the extraction.

## Verification

[CI](.github/workflows/lean.yml) builds from source, checks the exact statement, audits every bundled declaration—including private and generated declarations—against `propext`, `Classical.choice`, and `Quot.sound`, and replays the imported closure through the official Lean kernel. Logs and receipts are preserved on success and failure. Seven unchanged historical generated partial declarations are inventoried explicitly; official replay skips partial/unsafe constants. The main theorem must be safe. No separate NanoDa check is run.

Run the same checks from a clean committed checkout after obtaining the Mathlib cache:

```sh
python3 -B scripts/verification/verify.py --output /tmp/sawin-verification
```

References: [Sawin](https://arxiv.org/abs/2605.20579) and the [Remarks paper](https://arxiv.org/abs/2605.20695). 

## Authorship and AI assistance

Astra GPT-6 Codex assisted with Lean development, statement review, and preparation of this repository.
Naganori Yamaguchi is the human author and responsible maintainer.

Apache License 2.0. See [LICENSE](LICENSE).
