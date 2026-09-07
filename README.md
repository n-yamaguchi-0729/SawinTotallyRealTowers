# Sawin’s totally real tower in Lean 4

There is one infinite set of primes congruent to 1 modulo 4 that splits completely in totally real number fields of arbitrarily large degree, with root discriminant at most **255255**.

```lean
import SawinTotallyRealTowers.SawinTotallyRealTower

#check ClassFieldTower.Sawin.sawin_totally_real_tower
```

The [main theorem](Lean4/SawinTotallyRealTowers/SawinTotallyRealTower.lean) matches the [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/8323e878b83fcd7f4a448256069352a265460d75/FormalConjectures/ErdosProblems/90.lean#L193). [The API check](tests/Statement.lean) repeats that exact target.

[Martinet’s totally real towers](Lean4/SawinTotallyRealTowers/MartinetCorollary.lean) follow directly from the same Sawin theorem by forgetting the splitting conditions and rewriting the root-discriminant bound. The [API check](tests/MartinetStatement.lean) matches the [Lean Eval target](https://github.com/leanprover/lean-eval/blob/6b4b87b672f5301f24983a12fda65dac608453ce/generated/martinet_totally_real_towers/Challenge.lean).

```lean
import SawinTotallyRealTowers.MartinetCorollary

#check ClassFieldTower.Sawin.exists_totallyReal_discr_le
```

## Build

Lean **4.33.0**, Mathlib **6f1ef4e5dd604a435bddba4747b13970cd65d2a1**. Mathlib is the only direct external Git dependency; its dependencies are pinned in `lake-manifest.json`.

```sh
lake exe cache get
lake --wfail build
lake env lean --error=warning tests/Statement.lean
lake env lean --error=warning tests/MartinetStatement.lean
```

This repository bundles the **1,600 original local modules** needed for Sawin, plus **one Martinet corollary**. All 1,601 modules are reachable from the corollary’s imports, including the needed parts of CFT, PCG, GC, VFT, and Sawin. This is the file/import closure of these sources; no `All` aggregates or unrelated modules are included. [Source provenance and hashes](verification/source-manifest.json) record the extraction.

## Verification

The published [FC proof](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/blob/3a455e1aa9140dbbe7b7d68f508392a69c86d0f4/Lean4/SawinTotallyRealTowers/SawinTotallyRealTower.lean#L31) remains pinned to the original commit. The new Martinet corollary has received static review only; its build and proof checks are pending.

[CI](.github/workflows/lean.yml) builds from source, checks both exact statements, audits every bundled declaration—including private and generated declarations—against `propext`, `Classical.choice`, and `Quot.sound`, and replays the imported closure through the official Lean kernel. Logs and receipts are preserved on success and failure. Seven unchanged historical generated partial declarations are inventoried explicitly; official replay skips partial/unsafe constants. Both entry theorems must be safe. No separate NanoDa check is run.

Run the same checks from a clean committed checkout after obtaining the Mathlib cache:

```sh
python3 -B scripts/verification/verify.py --output /tmp/sawin-verification
```

References: [Sawin](https://arxiv.org/abs/2605.20579) and the [Remarks paper](https://arxiv.org/abs/2605.20695). Author: Naganori Yamaguchi. Developed with assistance from OpenAI Codex as part of the [Yamaguchi Lean 4 Library](https://n-yamaguchi-0729.github.io/YamaLean4Lib_pages/).

Apache License 2.0. See [LICENSE](LICENSE).
