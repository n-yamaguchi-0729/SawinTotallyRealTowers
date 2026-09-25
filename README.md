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
| Lean Eval: Shafarevich | [Shafarevich's relation-rank bound problem](https://leanprover.github.io/lean-eval-leaderboard/problems/shafarevich_relation_rank_bound/) ([source challenge](https://github.com/leanprover/lean-eval/blob/6b4b87b672f5301f24983a12fda65dac608453ce/generated/shafarevich_relation_rank_bound/Challenge.lean)) is represented by the [relation-rank theorem](Lean4/SawinTotallyRealTowers/UnramifiedProPRelationRank/RelationRank/ShafarevichRelationRankBound.lean). [Adapter lemmas](Lean4/SawinTotallyRealTowers/UnramifiedProPRelationRank/RelationRank/LeanEvalAdapter.lean) relate the library's representations to the benchmark. A submission was [accepted by Lean Eval](https://github.com/leanprover/lean-eval-submissions/blob/main/results/n-yamaguchi-0729.json). |

### Formal Conjectures: Sawin's totally real tower

This is the complete declaration and proof of the [Sawin theorem](Lean4/SawinTotallyRealTowers/SawinTotallyRealTower.lean). The linked source contains its imports and namespace context. The [exact statement check](tests/Statement.lean) matches the pinned Formal Conjectures target above.

```lean
theorem sawin_totally_real_tower :
    ∃ (rdBound : ℝ) (Q : Set ℕ), Q.Infinite ∧ (∀ q ∈ Q, q.Prime ∧ q % 4 = 1) ∧
      ∀ N : ℕ, ∃ (F : Type) (_ : Field F) (_ : CharZero F) (_ : NumberField F)
        (_ : IsTotallyReal F),
        N ≤ Module.finrank ℚ F ∧
        (|(NumberField.discr F : ℝ)|) ^ ((1 : ℝ) / Module.finrank ℚ F) ≤ rdBound ∧
        ∀ q ∈ Q, ∃ (factors : Finset (Ideal (𝓞 F))),
          factors.card = Module.finrank ℚ F ∧
          ∀ p ∈ factors, p.IsMaximal ∧ (q : 𝓞 F) ∈ p := by
  classical
  let instPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨primes, L, hGal, _, hInfinite, hL, hprimes, _, hsplit⟩ :=
    exists_sawinInfinite_totallyReal_split_field
  let Q : Set ℕ := Set.range (fun n : ℕ ↦ (primes n).val)
  have hQ : Q.Infinite :=
    Set.infinite_of_forall_exists_gt
      (fun a ↦ ⟨(primes a).val, ⟨a, rfl⟩, (hprimes a).1⟩)
  refine ⟨255255, Q, hQ, ?_, ?_⟩
  · rintro q ⟨n, rfl⟩
    exact ⟨(primes n).property, (hprimes n).2.2⟩
  · intro N
    obtain ⟨E, hE, hN⟩ :=
      @AlgebraicNumberTheory.exists_finiteGaloisIntermediateField_le_finrank_ge_of_infinite_aut
        ℚ (AlgebraicClosure ℚ) _ _ _ L hGal hInfinite N
    let instNumberFieldE : NumberField E := NumberField.of_module_finite ℚ E
    let instGalE : IsGalois ℚ E := E.isGalois
    have hAdm :=
      (isAdmissibleFiniteLayer_iff_le_maximalRealProPOutside
        2 sawinRationalPrimeSupport E).mpr (hE.trans hL)
    let instTotallyRealE : IsTotallyReal E :=
      (isUnramifiedAtInfinitePlaces_rat_iff_isTotallyReal E).mp hAdm.2.2
    have hdiscr := discr_natAbs_le_of_sawin_ramification E hAdm.1 hAdm.2.1
    have hroot := rootDiscr_le_of_natAbs_discr_le_pow E 255255 hdiscr
    refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, hN, ?_, ?_⟩
    · simpa only [NumberField.rootDiscr_def, Int.cast_abs, one_div, Nat.cast_ofNat] using hroot
    · rintro q ⟨n, rfl⟩
      exact exists_finset_maximalIdeals_of_finitePlaceSplitsCompletely
        E (primes n) (hsplit E hE n)
```

### Lean Eval: Martinet's totally real towers

This is the complete theorem endpoint from the accepted Lean Eval submission. Its `Submission.Vendor` import belongs to the submission package; the corresponding theorem in this repository is [`exists_totallyReal_discr_le`](Lean4/SawinTotallyRealTowers/MartinetCorollary.lean). The [exact statement check](tests/MartinetStatement.lean) also typechecks against the public theorem.

```lean
import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Vendor.SawinTotallyRealTowers.MartinetCorollary

set_option autoImplicit false

open NumberField

namespace Submission

theorem exists_totallyReal_discr_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d := by
  exact ClassFieldTower.Sawin.exists_totallyReal_discr_le

end Submission
```

### Lean Eval: Shafarevich's relation-rank bound

This is the complete theorem endpoint from the accepted Lean Eval submission. The submission-specific `ChallengeDeps` and `Submission.Helpers` modules supply the benchmark definitions and adapters; this block is the submitted endpoint, not a stand-alone file in this repository. The public [relation-rank theorem](Lean4/SawinTotallyRealTowers/UnramifiedProPRelationRank/RelationRank/ShafarevichRelationRankBound.lean) and [adapter](Lean4/SawinTotallyRealTowers/UnramifiedProPRelationRank/RelationRank/LeanEvalAdapter.lean) contain the supporting development.

```lean
import ChallengeDeps
import Submission.Helpers

set_option autoImplicit false

open LeanEval.NumberTheory
open NumberField CategoryTheory

namespace Submission

theorem shafarevich_relation_rank_bound (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (_hpOdd : Odd p) :
    H2Finite p (MaxUnramifiedProPGaloisGroup F p) ∧
      (open Classical in
       relationRank p (MaxUnramifiedProPGaloisGroup F p) ≤
        generatorRank (MaxUnramifiedProPGaloisGroup F p) +
          (NumberField.InfinitePlace.nrRealPlaces F +
            NumberField.InfinitePlace.nrComplexPlaces F - 1) +
          (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0)) := by
  classical
  have h := ClassFieldTower.Martinet.Shafarevich.shafarevich_relation_rank_bound F p _hpOdd
  have hfield : ClassFieldTower.Martinet.maximalEverywhereUnramifiedProP F p =
      maximalUnramifiedProPF F p :=
    ClassFieldTower.Martinet.Shafarevich.maximalEverywhereUnramifiedProP_eq_explicit F p
  change FiniteDimensional (ZMod p)
      (ClassFieldTower.Cohomology.continuousCohomologyZModP p
        ((maximalUnramifiedProPF F p) ≃ₐ[F] (maximalUnramifiedProPF F p)) 2) ∧ _
  change FiniteDimensional (ZMod p)
      (ClassFieldTower.Cohomology.continuousCohomologyZModP p
        ((ClassFieldTower.Martinet.maximalEverywhereUnramifiedProP F p) ≃ₐ[F]
          (ClassFieldTower.Martinet.maximalEverywhereUnramifiedProP F p)) 2) ∧
    Module.finrank (ZMod p)
      (ClassFieldTower.Cohomology.continuousCohomologyZModP p
        ((ClassFieldTower.Martinet.maximalEverywhereUnramifiedProP F p) ≃ₐ[F]
          (ClassFieldTower.Martinet.maximalEverywhereUnramifiedProP F p)) 2) ≤
      ClassFieldTower.ProP.finiteTopologicalGeneratorRank
        ((ClassFieldTower.Martinet.maximalEverywhereUnramifiedProP F p) ≃ₐ[F]
          (ClassFieldTower.Martinet.maximalEverywhereUnramifiedProP F p)) +
        (NumberField.InfinitePlace.nrRealPlaces F +
          NumberField.InfinitePlace.nrComplexPlaces F - 1) +
        (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0) at h
  rw [hfield] at h
  exact h

end Submission
```

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
the two default targets. The [source manifest](.github/verification/source-manifest.json)
records the initial extraction commit, each module's imports, and the current
source hashes.

## Verification

The earlier [public proof of the Formal Conjectures statement in this repository](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/blob/3a455e1aa9140dbbe7b7d68f508392a69c86d0f4/Lean4/SawinTotallyRealTowers/SawinTotallyRealTower.lean#L31)
and the accepted [Martinet and Shafarevich Lean Eval submissions](https://github.com/leanprover/lean-eval-submissions/blob/main/results/n-yamaguchi-0729.json)
refer to earlier versions of this repository. On 2026-09-08, the Martinet
submission passed a fresh build of all 1,602 solver files, the official
Comparator and NanoDa checks, and official Lean 4.33 kernel replay. Its
[evaluation CI](https://github.com/leanprover/lean-eval-submissions/actions/runs/34192301049)
passed. Those results predate the expanded Lean 4.34 source bundle.

[CI](.github/workflows/lean.yml) is configured to inventory all physical sources,
check the SHA-pinned import closure, build the two roots with warnings as errors,
compile the exact Formal Conjectures and Martinet statements, and audit every
bundled declaration for unexpected axioms, sorry, unsafe code, and new partial
declarations. It then exports the complete safe declaration union, checks it
with pinned NanoDa, replays the closure with the official Lean kernel, and
checks the three named public theorems against the compiled inventory. The
accepted Shafarevich benchmark uses submission-specific helpers; this CI
checks its public theorem, not that exact benchmark submission. The expanded
Lean 4.34 bundle has not yet completed this full CI pipeline.

The physical inventory and SHA-pinned closure can be checked without a build:

```sh
python3 -B .github/verification/generate_manifest.py \
  --root . --config .github/verification/manifest-config.json \
  --manifest /tmp/sawin-modules.json --report /tmp/sawin-source-audit.json
python3 -B .github/verification/check_source_closure.py \
  --generated-manifest /tmp/sawin-modules.json
```

The complete pipeline requires a clean committed checkout, the pinned Mathlib
cache, and the pinned exporter and NanoDa tools. Its commands and artifact
paths are in [the workflow](.github/workflows/lean.yml) and explained in
[verification notes](.github/verification/README.md).

## Authorship and AI assistance

Astra GPT-6 Codex assisted with Lean development, statement review, and
preparation of this repository. [Naganori Yamaguchi](https://github.com/n-yamaguchi-0729)
is the human author and responsible maintainer. The benchmark statements and
their source licenses are credited in the corresponding Lean files.

## License

Apache License 2.0. See [LICENSE](LICENSE).
