import ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Projections

set_option autoImplicit false

/-!
# Completed Group Algebra / Basic / All Finite / Topology

This module transports the finite-stage topological ring and scalar-action structures through the
single all-finite inverse limit, and records its compactness and separation properties.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

local instance (U : CompletedGroupAlgebraIndex G) :
    Ring ((completedGroupAlgebraSystem R G).X U) := by
  change Ring (CompletedGroupAlgebraStage R G U)
  infer_instance

local instance (U : CompletedGroupAlgebraIndex G) :
    Module R ((completedGroupAlgebraSystem R G).X U) := by
  change Module R (CompletedGroupAlgebraStage R G U)
  infer_instance

/-- Each finite stage \(R[G/U]\) is a topological ring for its product topology. -/
theorem completedGroupAlgebraStage_isTopologicalRing (U : CompletedGroupAlgebraIndex G) :
    IsTopologicalRing ((completedGroupAlgebraSystem R G).X U) := by
  dsimp [completedGroupAlgebraSystem, CompletedGroupAlgebraStage]
  exact finiteGroupAlgebra_isTopologicalRing R (CompletedGroupAlgebraQuotient G U)

/-- Each stage of the all-finite system has its finite product topological-ring structure. -/
instance instIsTopologicalRingCompletedGroupAlgebraSystemX
    (U : CompletedGroupAlgebraIndex G) :
    IsTopologicalRing ((completedGroupAlgebraSystem R G).X U) :=
  completedGroupAlgebraStage_isTopologicalRing (R := R) (G := G) U

/-- Scalar multiplication is continuous because it is continuous at every finite stage. -/
instance instContinuousSMulCompletedGroupAlgebra :
    ContinuousSMul R (CompletedGroupAlgebraCarrier R G) := by
  let stageContinuousSMul : ∀ U : CompletedGroupAlgebraIndex G,
      ContinuousSMul R ((completedGroupAlgebraSystem R G).X U) := fun U => by
    dsimp [completedGroupAlgebraSystem, CompletedGroupAlgebraStage]
    exact finiteGroupAlgebra_continuousSMul R (CompletedGroupAlgebraQuotient G U)
  exact @instContinuousSMulInverseLimitOfIsModuleSystem _ _
    (completedGroupAlgebraSystem R G)
    (fun U => @Ring.toAddCommGroup _
      (instRingCompletedGroupAlgebraSystemStage (G := G) (R := R) U))
    R inferInstance
    (fun U => instModuleCompletedGroupAlgebraSystemStage (G := G) (R := R) U)
    (@IsModuleSystem.mk _ _ R _ (completedGroupAlgebraSystem R G)
      (fun U => @Ring.toAddCommGroup _
        (instRingCompletedGroupAlgebraSystemStage (G := G) (R := R) U))
      (fun U => instModuleCompletedGroupAlgebraSystemStage (G := G) (R := R) U)
      (completedGroupAlgebraTransition_smul (R := R) (G := G)))
    inferInstance stageContinuousSMul

/-- The completed group algebra inherits its topological-ring structure from the generic
ring-valued inverse limit. -/
instance instIsTopologicalRingCompletedGroupAlgebra :
    IsTopologicalRing (CompletedGroupAlgebraCarrier R G) := by
  exact inferInstanceAs
    (IsTopologicalRing (completedGroupAlgebraSystem R G).inverseLimit)

/-- The completed group algebra is compact for compact Hausdorff coefficients. -/
theorem completedGroupAlgebra_compactSpace [CompactSpace R] [T2Space R] :
    CompactSpace (CompletedGroupAlgebraCarrier R G) := by
  let : ∀ U : CompletedGroupAlgebraIndex G,
      CompactSpace ((completedGroupAlgebraSystem R G).X U) := fun U =>
    by
      dsimp [completedGroupAlgebraSystem, CompletedGroupAlgebraStage]
      exact finiteGroupAlgebra_compactSpace R (CompletedGroupAlgebraQuotient G U)
  let : ∀ U : CompletedGroupAlgebraIndex G,
      T2Space ((completedGroupAlgebraSystem R G).X U) := fun U =>
    by
      dsimp [completedGroupAlgebraSystem, CompletedGroupAlgebraStage]
      exact finiteGroupAlgebra_t2Space R (CompletedGroupAlgebraQuotient G U)
  change CompactSpace (completedGroupAlgebraSystem R G).inverseLimit
  infer_instance

/-- The completed group algebra is Hausdorff for Hausdorff coefficients. -/
theorem completedGroupAlgebra_t2Space [T2Space R] :
    T2Space (CompletedGroupAlgebraCarrier R G) := by
  let : ∀ U : CompletedGroupAlgebraIndex G,
      T2Space ((completedGroupAlgebraSystem R G).X U) := fun U =>
    by
      dsimp [completedGroupAlgebraSystem, CompletedGroupAlgebraStage]
      exact finiteGroupAlgebra_t2Space R (CompletedGroupAlgebraQuotient G U)
  exact (completedGroupAlgebraSystem R G).t2Space_inverseLimit

/-- The completed group algebra is totally disconnected for totally disconnected coefficients. -/
theorem completedGroupAlgebra_totallyDisconnectedSpace [TotallyDisconnectedSpace R] :
    TotallyDisconnectedSpace (CompletedGroupAlgebraCarrier R G) := by
  let : ∀ U : CompletedGroupAlgebraIndex G,
      TotallyDisconnectedSpace ((completedGroupAlgebraSystem R G).X U) := fun U =>
    by
      dsimp [completedGroupAlgebraSystem, CompletedGroupAlgebraStage]
      exact finiteGroupAlgebra_totallyDisconnectedSpace R
        (CompletedGroupAlgebraQuotient G U)
  exact (completedGroupAlgebraSystem R G).totallyDisconnectedSpace_inverseLimit

end

end CompletedGroupAlgebra
