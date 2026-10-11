/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.ContinuousH1InflationExact
import Nyll.GaloisCohomology.ProP.InflationTransgressionExact

/-!
# Continuous low-degree five-term exact sequence

The three kernel--range identities for inflation, restriction, and transgression assemble into
the continuous low-degree five-term sequence with trivial `ZMod p` coefficients.
-/

open scoped Topology

namespace ClassFieldTower.Cohomology

open ProCGroups ProCGroups.ProC
open ClassFieldTower.ProP

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance continuousFiveTermH1Module
    {q : ℕ} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := H)) :=
  continuousH1ZModModule

/-- Exactness at the three middle terms of the continuous low-degree sequence

`H¹(G/U) → H¹(G) → H¹(U)ᴳ → H²(G/U) → H²(G)`.
-/
theorem continuousLowDegreeFiveTerm_exact
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    Function.Exact
        (continuousH1InflationLinearMap U)
        (continuousCharacterRestrictionLinearMap U) ∧
      Function.Exact
        (continuousCharacterRestrictionLinearMap U)
        (continuousTransgressionLinearMap U) ∧
      Function.Exact
        (continuousTransgressionLinearMap U)
        (degreeTwoInflationLinearMap U) := by
  refine ⟨LinearMap.exact_iff.mpr ?_, LinearMap.exact_iff.mpr ?_,
    LinearMap.exact_iff.mpr ?_⟩
  · exact (continuousH1Inflation_range_eq_characterRestriction_ker U).symm
  · exact (continuousCharacterRestriction_range_eq_transgression_ker U).symm
  · exact (continuousTransgression_range_eq_degreeTwoInflation_ker U).symm

end

end ClassFieldTower.Cohomology
