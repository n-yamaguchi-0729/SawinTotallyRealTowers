/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.InflationTransgressionExact
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Quotient presentation of a degree-two inflation range

The inflation--transgression kernel calculation identifies finite-stage degree-two cohomology
modulo continuous transgression with the corresponding range in ambient degree-two cohomology.
-/

open CategoryTheory TopRep ContRepresentation
open scoped Topology

namespace ClassFieldTower.Cohomology

open ProCGroups ProCGroups.ProC

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The first isomorphism theorem for degree-two inflation, with its kernel rewritten as the
range of continuous transgression. -/
noncomputable def degreeTwoQuotientTransgressionEquivInflationRange
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    (continuousCohomologyZModPLifted p (G ⧸ (U.1 : Subgroup G)) 2 ⧸
        LinearMap.range (continuousTransgressionLinearMap U)) ≃ₗ[ZMod p]
      degreeTwoInflationRange (p := p) U :=
  (Submodule.quotEquivOfEq _ _
      (continuousTransgression_range_eq_degreeTwoInflation_ker U)).trans
    (degreeTwoInflationLinearMap U).quotKerEquivRange

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp]
theorem degreeTwoQuotientTransgressionEquivInflationRange_apply_mk
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (x : continuousCohomologyZModPLifted p (G ⧸ (U.1 : Subgroup G)) 2) :
    degreeTwoQuotientTransgressionEquivInflationRange U
        (Submodule.Quotient.mk x) =
      ⟨degreeTwoInflationLinearMap U x,
        LinearMap.mem_range_self (degreeTwoInflationLinearMap U) x⟩ := by
  rfl

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Finite-stage degree-two cohomology modulo continuous transgression and its ambient
inflation range have equal `ZMod p`-dimension. -/
theorem finrank_degreeTwoQuotientTransgression_eq_inflationRange
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    Module.finrank (ZMod p)
        (continuousCohomologyZModPLifted p (G ⧸ (U.1 : Subgroup G)) 2 ⧸
          LinearMap.range (continuousTransgressionLinearMap U)) =
      Module.finrank (ZMod p) (degreeTwoInflationRange (p := p) U) :=
  (degreeTwoQuotientTransgressionEquivInflationRange U).finrank_eq

end

end ClassFieldTower.Cohomology
