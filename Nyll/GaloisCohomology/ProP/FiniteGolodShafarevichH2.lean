/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.FinitePresentationExistence
import Nyll.GaloisCohomology.ProP.H2FiniteStageFamily
import Nyll.GaloisCohomology.ProP.RelationRankH2
import Nyll.GaloisCohomology.ProP.TrivialZModP
import Nyll.ProCGroups.FiniteGeneration.Basic
import Nyll.ProCGroups.GolodShafarevich.FiniteCriterion
import Nyll.ProCGroups.ProC.InverseLimits.Predicates
import Nyll.ProCGroups.ProP.GeneratorRank
import Nyll.ProCGroups.ProP.Presentation.RelationCardinal
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Finite Golod--Shafarevich bound in terms of H²

For a finite nontrivial pro-p group, finite cochains supply finite-dimensional H² and the
constructed finite minimal presentation identifies its relation rank with that dimension.
Thus no presentation or finite-presentation hypothesis is required in the numerical bound.
-/

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.FiniteGeneration ClassFieldTower.Cohomology

universe u

/-- A finite nontrivial pro-p group satisfies the strict Golod--Shafarevich inequality
with its actual degree-two continuous cohomology dimension. -/
theorem finite_sq_generatorRank_lt_four_mul_finrank_h2
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] [T2Space G] [Finite G] [Nontrivial G]
    (hG : ProC.HasPGroupOpenNormalBasis p G) :
    topologicalGeneratorRank G ^ 2 < 4 * Module.finrank (ZMod p)
      (continuousCohomologyZModPLifted p G 2) := by
  have hfg : TopologicallyFinitelyGenerated G := topologicallyFinitelyGenerated_of_finite
  let : FiniteDimensional (ZMod p) (continuousCohomologyZModPLifted p G 2) :=
    finiteDimensional_degree_two_of_finite (inferInstance : Finite G)
  have hP : HasFiniteMinimalPresentation p G :=
    hasFiniteMinimalPresentation_of_finiteDimensional_h2 hG hfg
  simpa only [minimalRelationRank_eq_h2Rank hP, h2Rank_eq_finrank] using
    finite_sq_generatorRank_lt_four_mul_relationRank hP

end ClassFieldTower.ProP
