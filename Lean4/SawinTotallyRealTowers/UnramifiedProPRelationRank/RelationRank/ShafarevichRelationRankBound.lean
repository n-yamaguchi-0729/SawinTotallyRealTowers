/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Statement adapted from Lean Eval:
https://github.com/leanprover/lean-eval/blob/4ae7061fe4b0b70dcb7fe24fdee067b68636226b/generated/shafarevich_relation_rank_bound/Challenge.lean
Lean Eval repository: Copyright 2026 Lean FRO, LLC; Apache 2.0.
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2RadicalEmbedding
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.IdealPowerRadicalH2Bound
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.LeanEvalAdapter

set_option autoImplicit false
/-!
# Shafarevich's relation-rank bound

For every number field and every odd prime, the maximal everywhere-unramified
pro-p Galois group has finite-dimensional H². Its relation rank is at most
the generator rank plus the unit rank and the roots-of-unity correction.
All arithmetic input is supplied by the constructed finite-stage radical
maps and their proved kernel bounds.
-/

open scoped NumberField Topology
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology ClassFieldTower.ProP ClassFieldTower.Martinet
open ProCGroups.Generation ProCGroups.FiniteGeneration

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime] (hpOdd : Odd p)

include hpOdd

/-- The actual maximal unramified H² is finite and bounded by the arithmetic radical dual. -/
theorem maxEverywhereUnramified_h2_finite_and_finrank_le_radicalDual :
    FiniteDimensional (ZMod p)
      (continuousCohomologyZModPLifted p (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ∧
    Module.finrank (ZMod p)
      (continuousCohomologyZModPLifted p (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ≤
        Module.finrank (ZMod p) (Module.Dual (ZMod p) (idealPowerRadicalModP F p)) := by
  let : FiniteDimensional (ZMod p) (Module.Dual (ZMod p) (idealPowerRadicalModP F p)) :=
    idealPowerRadicalModPDual_finiteDimensional F p
  exact finiteDimensional_and_finrank_degree_two_le_of_inflationRange_embeddings
    (p := p) (G := MaxEverywhereUnramifiedProPGaloisGroup F p)
    (W := Module.Dual (ZMod p) (idealPowerRadicalModP F p))
    (maxEverywhereUnramifiedProPGaloisGroup_hasPGroupOpenNormalBasis F p hpOdd)
    (@arithmeticStageH2InflationRange_exists_radicalDual_embedding
      F _ _ (p.toPNat (Fact.out : p.Prime).pos) (inferInstance : Fact p.Prime) hpOdd)

/-- Shafarevich's bound in the universe-lifted continuous-cohomology model. -/
theorem shafarevich_relation_rank_bound_lifted :
    FiniteDimensional (ZMod p)
      (continuousCohomologyZModPLifted p (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ∧
    (open Classical in
      Module.finrank (ZMod p)
        (continuousCohomologyZModPLifted p (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ≤
      topologicalGeneratorRank (MaxEverywhereUnramifiedProPGaloisGroup F p) +
        (NumberField.InfinitePlace.nrRealPlaces F + NumberField.InfinitePlace.nrComplexPlaces F - 1) +
          (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0)) := by
  obtain ⟨hfinite, hle⟩ := maxEverywhereUnramified_h2_finite_and_finrank_le_radicalDual F p hpOdd
  exact maxEverywhereUnramified_h2_numerical_bound_of_finrank_le_radicalDual F p hpOdd hfinite hle

/-- Shafarevich's bound with ordinary coefficients and finite-set generator rank. -/
theorem shafarevich_relation_rank_bound :
    FiniteDimensional (ZMod p)
      (continuousCohomologyZModP p (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ∧
    (open Classical in
      Module.finrank (ZMod p)
        (continuousCohomologyZModP p (MaxEverywhereUnramifiedProPGaloisGroup F p) 2) ≤
      finiteTopologicalGeneratorRank (MaxEverywhereUnramifiedProPGaloisGroup F p) +
        (NumberField.InfinitePlace.nrRealPlaces F + NumberField.InfinitePlace.nrComplexPlaces F - 1) +
          (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0)) := by
  classical
  exact maxEverywhereUnramified_smallH2_and_finiteGeneratorRank_bound_of_lifted F p hpOdd
    (NumberField.InfinitePlace.nrRealPlaces F + NumberField.InfinitePlace.nrComplexPlaces F - 1)
    (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0)
    (shafarevich_relation_rank_bound_lifted F p hpOdd)

end ClassFieldTower.Martinet.Shafarevich
