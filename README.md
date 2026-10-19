# Sawin's totally real towers (Lean 4.35.0-rc2)

[![Lean](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

This Lean component of [NYLL](https://github.com/n-yamaguchi-0729/NYLL) develops Sawin’s theorem on totally real fields
of unbounded degree and bounded root discriminant, together with Martinet’s
corollary and Shafarevich’s relation-rank bound. The [mathematical guide](https://n-yamaguchi-0729.github.io/NYLL/libraries/sawin-totally-real-towers/) describes these
three results and their relationship to the formalized benchmark statements.

## Main results

| Result | Mathematical content |
| --- | --- |
| [Sawin's totally real tower](Nyll/SawinTotallyRealTowers/SawinTotallyRealTower.lean) | One infinite prime set splits completely in totally real fields of unbounded degree with root discriminant at most 255255. |
| [Martinet's discriminant bound](Nyll/SawinTotallyRealTowers/MartinetCorollary.lean) | Totally real fields of arbitrarily large degree satisfy a uniform exponential discriminant bound. |
| [Shafarevich's relation-rank bound](Nyll/SawinTotallyRealTowers/UnramifiedProPRelationRank/RelationRank/ShafarevichRelationRankBound.lean) | For odd `p`, bounds the relation rank of the maximal everywhere-unramified pro-`p` Galois group by its generator rank, the unit rank, and the roots-of-unity correction. |

## Public API

Use [leanprover/lean4:v4.35.0-rc2](lean-toolchain) and the Mathlib revision pinned in
[lake-manifest.json](lake-manifest.json). Add this dependency to your project’s
lakefile.toml:

```toml
[[require]]
name = "Nyll"
git = "https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers.git"
rev = "main"
```

Run `lake update Nyll`, then commit your generated lake-manifest.json to retain
the resolved revisions. Import the library in a Lean file:

```lean
import Nyll.SawinTotallyRealTowers.All
```

The standalone distributions share the package name Nyll. Choose one distribution;
for several libraries together, use [NYLL](https://github.com/n-yamaguchi-0729/NYLL).

To build a checkout of this repository, run from its root:

```sh
lake exe cache get
lake --wfail build
```

## Verification

The accepted [Martinet and Shafarevich Lean Eval submissions](https://github.com/leanprover/lean-eval-submissions/blob/main/results/n-yamaguchi-0729.json)
and the [earlier Sawin proof](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/blob/3a455e1aa9140dbbe7b7d68f508392a69c86d0f4/Lean4/SawinTotallyRealTowers/SawinTotallyRealTower.lean#L31)
concern earlier revisions.

[CI](.github/workflows/lean.yml) builds the current import closure with warnings
as errors and verifies proofs with NanoDa and the Lean kernel. It checks the
Formal Conjectures and Martinet benchmark statements, and the public
Shafarevich theorem. The latter has a different interface from the accepted
submission. See the [verification notes](.github/verification/README.md)
for the source audit and verification commands.

## Authorship

All original code in this library is written by OpenAI Codex.

[Naganori Yamaguchi](https://github.com/n-yamaguchi-0729) sets the mathematical
goals and scope, directs development, and maintains the library.
The benchmark statements and their source licenses are credited in the
corresponding Lean files.

## License

<!-- nyll-publication:credits:begin -->
Apache License 2.0. See [LICENSE](LICENSE).

Additional source-specific credits are preserved in [NOTICE](NOTICE).
<!-- nyll-publication:credits:end -->
