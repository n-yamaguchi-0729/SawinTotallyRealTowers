# Sawin's totally real towers in Lean 4

[![Lean](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Lean 4 library centered on Sawin's totally real tower theorem. One infinite
set of primes congruent to 1 modulo 4 splits completely in totally real
number fields of arbitrarily large degree, with root discriminant at most
**255255**. The library also contains Martinet's totally real tower corollary
and a development of Shafarevich's relation-rank bound.

## Public API

Import the Sawin theorem:

```lean
import SawinTotallyRealTowers.SawinTotallyRealTower

#check ClassFieldTower.Sawin.sawin_totally_real_tower
```

Import the Martinet corollary:

```lean
import SawinTotallyRealTowers.MartinetCorollary

#check ClassFieldTower.Sawin.exists_totallyReal_discr_le
```

Import the relation-rank theorem:

```lean
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ShafarevichRelationRankBound

#check ClassFieldTower.Martinet.Shafarevich.shafarevich_relation_rank_bound
```

Import the whole maintained Sawin library:

```lean
import SawinTotallyRealTowers.All
```

## Main results

| Result | Mathematical content |
| --- | --- |
| [`sawin_totally_real_tower`](Lean4/SawinTotallyRealTowers/SawinTotallyRealTower.lean) | One infinite prime set splits completely in totally real fields of unbounded degree with bounded root discriminant. |
| [`exists_totallyReal_discr_le`](Lean4/SawinTotallyRealTowers/MartinetCorollary.lean) | Totally real fields of arbitrarily large degree satisfy a uniform exponential discriminant bound. |
| [`shafarevich_relation_rank_bound`](Lean4/SawinTotallyRealTowers/UnramifiedProPRelationRank/RelationRank/ShafarevichRelationRankBound.lean) | For odd `p`, bounds the relation rank of the maximal everywhere-unramified pro-`p` Galois group by its generator rank, the unit rank, and the roots-of-unity correction. |

## Problem statements and related projects

This repository develops proofs for mathematical statements also published as
challenges by [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
and [Lean Eval](https://github.com/leanprover/lean-eval). The benchmark
statements are adapted with attribution in the corresponding Lean files. The
proofs and supporting library are developed here.

| Project | Statement and route to the library |
| --- | --- |
| Formal Conjectures | [Sawin's totally real tower theorem](https://google-deepmind.github.io/formal-conjectures/theorem/?name=Erdos90.sawin_totally_real_tower) ([source statement](https://github.com/google-deepmind/formal-conjectures/blob/8323e878b83fcd7f4a448256069352a265460d75/FormalConjectures/ErdosProblems/90.lean#L193)) is proved by [the Sawin theorem](Lean4/SawinTotallyRealTowers/SawinTotallyRealTower.lean). The [API check](tests/Statement.lean) tests the exact target. |
| Lean Eval: Martinet | [Martinet's totally real towers problem](https://leanprover.github.io/lean-eval-leaderboard/problems/martinet_totally_real_towers/) ([source challenge](https://github.com/leanprover/lean-eval/blob/6b4b87b672f5301f24983a12fda65dac608453ce/generated/martinet_totally_real_towers/Challenge.lean)) follows from [the Sawin theorem](Lean4/SawinTotallyRealTowers/MartinetCorollary.lean). The [API check](tests/MartinetStatement.lean) tests the exact target; a submission was [accepted by Lean Eval](https://github.com/leanprover/lean-eval-submissions/blob/main/results/n-yamaguchi-0729.json). |
| Lean Eval: Shafarevich | [Shafarevich's relation-rank bound problem](https://leanprover.github.io/lean-eval-leaderboard/problems/shafarevich_relation_rank_bound/) ([source challenge](https://github.com/leanprover/lean-eval/blob/4ae7061fe4b0b70dcb7fe24fdee067b68636226b/generated/shafarevich_relation_rank_bound/Challenge.lean)) motivates the [relation-rank theorem](Lean4/SawinTotallyRealTowers/UnramifiedProPRelationRank/RelationRank/ShafarevichRelationRankBound.lean). [Adapter lemmas](Lean4/SawinTotallyRealTowers/UnramifiedProPRelationRank/RelationRank/LeanEvalAdapter.lean) relate the library's representations to the benchmark. This repository does not claim a separately accepted submission for this target. |

See [Naganori Yamaguchi's Lean 4 projects](https://n-yamaguchi-0729.github.io/homepage-jp)
for links to these challenge pages and to the related ProCGroups and
ClassFieldTheory libraries. Mathematical references: [Sawin's paper](https://arxiv.org/abs/2605.20579)
and the [Remarks paper](https://arxiv.org/abs/2605.20695).

## Build

This repository pins Lean **4.34.0** and Mathlib
**5ed2965256430c3649e86755f9576b54eca72435**. Mathlib is the only direct
external Git dependency; its dependencies are pinned in
[`lake-manifest.json`](lake-manifest.json).

```sh
lake exe cache get
lake --wfail build
lake env lean --error=warning tests/Statement.lean
lake env lean --error=warning tests/MartinetStatement.lean
```

The repository contains **269 Sawin modules**: 268 from the maintained
workspace, including `SawinTotallyRealTowers.All`, and the standalone
Martinet corollary. Their imports require **1,471 bundled support modules**
from CFT, PCG, GC, and VFT. All **1,740** local modules are reachable from
the two default targets. The [source manifest](verification/source-manifest.json)
records the initial extraction commit, each module's imports, and the current
source hashes.

## Verification

The published [Formal Conjectures proof](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/blob/3a455e1aa9140dbbe7b7d68f508392a69c86d0f4/Lean4/SawinTotallyRealTowers/SawinTotallyRealTower.lean#L31)
and the accepted [Martinet Lean Eval submission](https://github.com/leanprover/lean-eval-submissions/blob/main/results/n-yamaguchi-0729.json)
refer to earlier versions of this repository. On 2026-09-08, the Martinet
submission passed a fresh build of all 1,602 solver files, the official
Comparator and NanoDa checks, and official Lean 4.33 kernel replay. Its
[evaluation CI](https://github.com/leanprover/lean-eval-submissions/actions/runs/34192301049)
passed. Those results predate the expanded Lean 4.34 source bundle.

[CI](.github/workflows/lean.yml) is configured to build from source, check
both exact benchmark statements, audit bundled declarations for unexpected
axioms, and replay the imported closure through the official Lean kernel.
Its independent verification results for the expanded bundle must be checked
after publication. The SHA-pinned import closure can be audited locally with:

```sh
python3 -B scripts/verification/check_source_closure.py
```

The complete verification pipeline additionally requires the Mathlib cache:

```sh
python3 -B scripts/verification/verify.py --output /tmp/sawin-verification
```

## Authorship and AI assistance

Astra GPT-6 Codex assisted with Lean development, statement review, and
preparation of this repository. [Naganori Yamaguchi](https://github.com/n-yamaguchi-0729)
is the human author and responsible maintainer. The benchmark statements and
their source licenses are credited in the corresponding Lean files.

## License

Apache License 2.0. See [LICENSE](LICENSE).
