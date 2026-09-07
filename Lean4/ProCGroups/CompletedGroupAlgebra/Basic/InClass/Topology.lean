import ProCGroups.CompletedGroupAlgebra.Basic.InClass.Projection

set_option autoImplicit false

/-!
# Completed Group Algebra / Basic / Within a Class / Topology

This module transports finite-stage topological structures through the named \(C\)-indexed
inverse-limit carrier and records its compactness and separation properties.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v w

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

local instance
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) :
    Ring ((completedGroupAlgebraSystemInClass C R G).X U) := by
  change Ring (CompletedGroupAlgebraStageInClass C R G U)
  infer_instance

local instance
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) :
    Module R ((completedGroupAlgebraSystemInClass C R G).X U) := by
  change Module R (CompletedGroupAlgebraStageInClass C R G U)
  infer_instance

/-- Each \(C\)-indexed finite stage is a topological ring. -/
theorem completedGroupAlgebraStageInClass_isTopologicalRing
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) :
    letI : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
      finite_completedGroupAlgebraQuotientInClass G C U
    letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
      (completedGroupAlgebraSystemInClass C R G).topologicalSpace U
    IsTopologicalRing (CompletedGroupAlgebraStageInClass C R G U) := by
  let : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
    finite_completedGroupAlgebraQuotientInClass G C U
  let : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    (completedGroupAlgebraSystemInClass C R G).topologicalSpace U
  dsimp [completedGroupAlgebraSystemInClass, CompletedGroupAlgebraStageInClass]
  exact finiteGroupAlgebra_isTopologicalRing R (CompletedGroupAlgebraQuotientInClass G C U)

/--
The inverse system of finite-stage group algebras inherits a ring structure from the compatible
finite-stage rings.
-/
instance instIsTopologicalRingCompletedGroupAlgebraSystemInClassX
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) :
    IsTopologicalRing ((completedGroupAlgebraSystemInClass C R G).X U) :=
  completedGroupAlgebraStageInClass_isTopologicalRing (R := R) (G := G) C U

/--
The \(C\)-indexed completed group algebra inherits a ring structure from the compatible
finite-stage rings.
-/
instance instIsTopologicalRingCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) :
    IsTopologicalRing (CompletedGroupAlgebraInClass C R G) := by
  change IsTopologicalRing (completedGroupAlgebraSystemInClass C R G).inverseLimit
  infer_instance

/-- Scalar multiplication is continuous for the relevant inverse-limit topology. -/
instance instContinuousSMulCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) :
    ContinuousSMul R (CompletedGroupAlgebraInClass C R G) := by
  let stageContinuousSMul : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      ContinuousSMul R ((completedGroupAlgebraSystemInClass C R G).X U) :=
    fun U => by
      let : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
        finite_completedGroupAlgebraQuotientInClass G C U
      dsimp [completedGroupAlgebraSystemInClass, CompletedGroupAlgebraStageInClass]
      exact finiteGroupAlgebra_continuousSMul R
        (CompletedGroupAlgebraQuotientInClass G C U)
  exact @instContinuousSMulInverseLimitOfIsModuleSystem _ _
    (completedGroupAlgebraSystemInClass C R G)
    (fun U => @Ring.toAddCommGroup _
      (instRingCompletedGroupAlgebraSystemInClassStage
        (G := G) (R := R) C U))
    R inferInstance
    (fun U => instModuleCompletedGroupAlgebraSystemInClassStage
      (G := G) (R := R) C U)
    (@IsModuleSystem.mk _ _ R _ (completedGroupAlgebraSystemInClass C R G)
      (fun U => @Ring.toAddCommGroup _
        (instRingCompletedGroupAlgebraSystemInClassStage
          (G := G) (R := R) C U))
      (fun U => instModuleCompletedGroupAlgebraSystemInClassStage
        (G := G) (R := R) C U)
      (completedGroupAlgebraTransitionInClass_smul (R := R) (G := G) C))
    inferInstance stageContinuousSMul

/-- The coefficient-ring map into the \(C\)-indexed completed group algebra is continuous. -/
theorem continuous_completedGroupAlgebraAlgebraMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) :
    Continuous (algebraMap R (CompletedGroupAlgebraInClass C R G)) := by
  let S := completedGroupAlgebraSystemInClass C R G
  let : ∀ U, TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    fun U => (completedGroupAlgebraSystemInClass C R G).topologicalSpace U
  let π : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      R → CompletedGroupAlgebraStageInClass C R G U :=
    fun U r => algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r
  have hπ : ∀ U, Continuous (π U) := by
    intro U
    let : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
      finite_completedGroupAlgebraQuotientInClass G C U
    exact finiteGroupAlgebra_algebraMap_continuous R
      (CompletedGroupAlgebraQuotientInClass G C U)
  have hcompat : S.CompatibleMaps π := by
    intro U V hUV
    funext r
    exact completedGroupAlgebraTransitionInClass_algebraMap
      (R := R) (G := G) C hUV r
  change Continuous (S.inverseLimitLift π hcompat)
  exact S.continuous_inverseLimitLift π hπ hcompat

/-- The \(C\)-indexed completed group algebra is compact for compact Hausdorff coefficients. -/
theorem completedGroupAlgebraInClass_compactSpace
    (C : ProCGroups.FiniteGroupClass.{v})
    [CompactSpace R] [T2Space R] :
    CompactSpace (CompletedGroupAlgebraInClass C R G) := by
  let S := completedGroupAlgebraSystemInClass C R G
  let : ∀ U : CompletedGroupAlgebraIndexInClass G C, CompactSpace (S.X U) := fun U =>
    by
      let : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
        finite_completedGroupAlgebraQuotientInClass G C U
      dsimp [S, completedGroupAlgebraSystemInClass, CompletedGroupAlgebraStageInClass]
      exact finiteGroupAlgebra_compactSpace R
        (CompletedGroupAlgebraQuotientInClass G C U)
  let : ∀ U : CompletedGroupAlgebraIndexInClass G C, T2Space (S.X U) := fun U =>
    by
      let : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
        finite_completedGroupAlgebraQuotientInClass G C U
      dsimp [S, completedGroupAlgebraSystemInClass, CompletedGroupAlgebraStageInClass]
      exact finiteGroupAlgebra_t2Space R
        (CompletedGroupAlgebraQuotientInClass G C U)
  change CompactSpace S.inverseLimit
  infer_instance

/-- The \(C\)-indexed completed group algebra is Hausdorff for Hausdorff coefficients. -/
theorem completedGroupAlgebraInClass_t2Space
    (C : ProCGroups.FiniteGroupClass.{v})
    [T2Space R] :
    T2Space (CompletedGroupAlgebraInClass C R G) := by
  let S := completedGroupAlgebraSystemInClass C R G
  let : ∀ U : CompletedGroupAlgebraIndexInClass G C, T2Space (S.X U) := fun U =>
    by
      let : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
        finite_completedGroupAlgebraQuotientInClass G C U
      dsimp [S, completedGroupAlgebraSystemInClass, CompletedGroupAlgebraStageInClass]
      exact finiteGroupAlgebra_t2Space R
        (CompletedGroupAlgebraQuotientInClass G C U)
  exact S.t2Space_inverseLimit

/--
The \(C\)-indexed completed group algebra is totally disconnected for totally disconnected
coefficients.
-/
theorem completedGroupAlgebraInClass_totallyDisconnectedSpace
    (C : ProCGroups.FiniteGroupClass.{v})
    [TotallyDisconnectedSpace R] :
    TotallyDisconnectedSpace (CompletedGroupAlgebraInClass C R G) := by
  let S := completedGroupAlgebraSystemInClass C R G
  let : ∀ U : CompletedGroupAlgebraIndexInClass G C, TotallyDisconnectedSpace (S.X U) :=
    fun U =>
      by
        let : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
          finite_completedGroupAlgebraQuotientInClass G C U
        dsimp [S, completedGroupAlgebraSystemInClass, CompletedGroupAlgebraStageInClass]
        exact finiteGroupAlgebra_totallyDisconnectedSpace R
          (CompletedGroupAlgebraQuotientInClass G C U)
  exact S.totallyDisconnectedSpace_inverseLimit


end

end CompletedGroupAlgebra
