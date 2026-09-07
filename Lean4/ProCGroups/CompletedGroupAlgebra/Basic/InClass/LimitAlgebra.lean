import ProCGroups.CompletedGroupAlgebra.Basic.InClass.System

set_option autoImplicit false

/-!
# Completed Group Algebra / Basic / Within a Class / Limit Algebra

This module gives the \(C\)-indexed completion the same opaque-carrier API as the all-finite
completion. Its inverse-limit representation is exchanged explicitly, while projections,
compatibility, and extensionality are the ordinary public interface. Algebraic structures are
inherited from the generic ring and module inverse limits.
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

/-- The \(C\)-indexed completed group algebra, kept opaque from its compatible-family
inverse-limit realization. -/
def CompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Type (max u v) :=
  (completedGroupAlgebraSystemInClass C R G).inverseLimit

/-- The \(C\)-indexed completion carries its inverse-limit topology. -/
instance instTopologicalSpaceCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) :
    TopologicalSpace (CompletedGroupAlgebraInClass C R G) :=
  inferInstanceAs
    (TopologicalSpace (completedGroupAlgebraSystemInClass C R G).inverseLimit)

/-- Explicit exchange between the named \(C\)-indexed carrier and its concrete compatible-family
realization. Ordinary code should use finite-stage projections instead. -/
def completedGroupAlgebraInClassCompatibleFamilyEquiv
    (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    CompletedGroupAlgebraInClass C R G ≃
      (completedGroupAlgebraSystemInClass C R G).inverseLimit :=
  Equiv.refl _

local instance instRingCompletedGroupAlgebraSystemInClassStage
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) :
    Ring ((completedGroupAlgebraSystemInClass C R G).X U) := by
  change Ring (CompletedGroupAlgebraStageInClass C R G U)
  infer_instance

local instance instModuleCompletedGroupAlgebraSystemInClassStage
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) :
    Module R ((completedGroupAlgebraSystemInClass C R G).X U) := by
  change Module R (CompletedGroupAlgebraStageInClass C R G U)
  infer_instance

/-- The \(C\)-indexed ring structure is inherited from the generic ring inverse limit. -/
instance instRingCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) :
    Ring (CompletedGroupAlgebraInClass C R G) :=
  inferInstanceAs (Ring (completedGroupAlgebraSystemInClass C R G).inverseLimit)

/-- The canonical \(C\)-indexed finite-stage projection, bundled at its source as a ring
homomorphism. -/
def completedGroupAlgebraProjectionInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraInClass C R G →+*
      CompletedGroupAlgebraStageInClass C R G U :=
  projectionRingHom (S := completedGroupAlgebraSystemInClass C R G) U

/-- The \(C\)-indexed bundled projections satisfy the transition compatibility equations. -/
theorem completedGroupAlgebraProjectionInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (x : CompletedGroupAlgebraInClass C R G) :
    completedGroupAlgebraTransitionInClass C R G hUV
        (completedGroupAlgebraProjectionInClass C R G V x) =
      completedGroupAlgebraProjectionInClass C R G U x :=
  (completedGroupAlgebraSystemInClass C R G).projection_compatible
    (completedGroupAlgebraInClassCompatibleFamilyEquiv
      (R := R) (G := G) C x) U V hUV

/-- \(C\)-indexed completed elements are equal when all bundled stage projections agree. -/
@[ext]
theorem completedGroupAlgebraInClass_ext
    (C : ProCGroups.FiniteGroupClass.{v})
    {x y : CompletedGroupAlgebraInClass C R G}
    (h : ∀ U, completedGroupAlgebraProjectionInClass C R G U x =
      completedGroupAlgebraProjectionInClass C R G U y) :
    x = y := by
  apply (completedGroupAlgebraInClassCompatibleFamilyEquiv
    (R := R) (G := G) C).injective
  apply (completedGroupAlgebraSystemInClass C R G).ext
  exact h

/-- The \(C\)-indexed tower is a module-valued inverse system over the coefficient ring. -/
instance instIsModuleSystemCompletedGroupAlgebraSystemInClass
    (C : ProCGroups.FiniteGroupClass.{v}) :
    @IsModuleSystem _ _ R _ (completedGroupAlgebraSystemInClass C R G)
      (fun U => @Ring.toAddCommGroup _
        (instRingCompletedGroupAlgebraSystemInClassStage
          (G := G) (R := R) C U))
      (fun U => instModuleCompletedGroupAlgebraSystemInClassStage
        (G := G) (R := R) C U) :=
  @IsModuleSystem.mk _ _ R _ (completedGroupAlgebraSystemInClass C R G)
    (fun U => @Ring.toAddCommGroup _
      (instRingCompletedGroupAlgebraSystemInClassStage
        (G := G) (R := R) C U))
    (fun U => instModuleCompletedGroupAlgebraSystemInClassStage
      (G := G) (R := R) C U)
    (completedGroupAlgebraTransitionInClass_smul (R := R) (G := G) C)

/-- The \(C\)-indexed module structure is inherited from the generic module inverse limit. -/
instance instModuleCoeffCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) :
    Module R (CompletedGroupAlgebraInClass C R G) := by
  change Module R (completedGroupAlgebraSystemInClass C R G).inverseLimit
  exact @instModuleInverseLimitOfIsModuleSystem
    _ _ (completedGroupAlgebraSystemInClass C R G)
    (fun U => @Ring.toAddCommGroup _
      (instRingCompletedGroupAlgebraSystemInClassStage
        (G := G) (R := R) C U))
    (@isAddGroupSystemOfIsRingSystem _ _ (completedGroupAlgebraSystemInClass C R G)
      (fun U => instRingCompletedGroupAlgebraSystemInClassStage
        (G := G) (R := R) C U)
      (instIsRingSystemCompletedGroupAlgebraSystemInClass G R C))
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

/-- Stagewise coefficient change on the \(C\)-indexed completion. -/
def completedGroupAlgebraCoeffMapInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (S : Type w) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) :
    CompletedGroupAlgebraInClass C R G →+*
      CompletedGroupAlgebraInClass C S G where
  toFun x :=
    (completedGroupAlgebraInClassCompatibleFamilyEquiv
      (R := S) (G := G) C).symm
      ((completedGroupAlgebraSystemInClass C S G).inverseLimitLift
        (fun U x =>
          completedGroupAlgebraStageCoeffMapInClass
            (R := R) (G := G) C S f U
            (completedGroupAlgebraProjectionInClass C R G U x))
        (by
          intro U V hUV
          funext x
          have hcompat := congrFun
            (congrArg DFunLike.coe
              (completedGroupAlgebraStageCoeffMapInClass_compatible
                (R := R) (G := G) C S f hUV))
            (completedGroupAlgebraProjectionInClass C R G V x)
          calc
            completedGroupAlgebraTransitionInClass C S G hUV
                (completedGroupAlgebraStageCoeffMapInClass
                  (R := R) (G := G) C S f V
                  (completedGroupAlgebraProjectionInClass C R G V x))
                =
              completedGroupAlgebraStageCoeffMapInClass
                (R := R) (G := G) C S f U
                (completedGroupAlgebraTransitionInClass C R G hUV
                  (completedGroupAlgebraProjectionInClass C R G V x)) :=
                    hcompat.symm
            _ =
              completedGroupAlgebraStageCoeffMapInClass
                (R := R) (G := G) C S f U
                (completedGroupAlgebraProjectionInClass C R G U x) := by
                  rw [completedGroupAlgebraProjectionInClass_compatible]) x)
  map_zero' := by
    apply completedGroupAlgebraInClass_ext (R := S) (G := G) C
    intro U
    exact map_zero
      (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U)
  map_one' := by
    apply completedGroupAlgebraInClass_ext (R := S) (G := G) C
    intro U
    exact map_one
      (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U)
  map_add' x y := by
    apply completedGroupAlgebraInClass_ext (R := S) (G := G) C
    intro U
    exact map_add
      (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U)
      (completedGroupAlgebraProjectionInClass C R G U x)
      (completedGroupAlgebraProjectionInClass C R G U y)
  map_mul' x y := by
    apply completedGroupAlgebraInClass_ext (R := S) (G := G) C
    intro U
    exact map_mul
      (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U)
      (completedGroupAlgebraProjectionInClass C R G U x)
      (completedGroupAlgebraProjectionInClass C R G U y)

/-- The coefficient-ring map is the inverse-limit lift of the \(C\)-indexed stage algebra maps. -/
def completedGroupAlgebraAlgebraMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) :
    R →+* CompletedGroupAlgebraInClass C R G where
  toFun r :=
    (completedGroupAlgebraInClassCompatibleFamilyEquiv
      (R := R) (G := G) C).symm
      ((completedGroupAlgebraSystemInClass C R G).inverseLimitLift
        (fun U r => algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r)
        (by
          intro U V hUV
          funext r
          exact completedGroupAlgebraTransitionInClass_algebraMap
            (R := R) (G := G) C hUV r) r)
  map_zero' := by
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    exact map_zero (algebraMap R (CompletedGroupAlgebraStageInClass C R G U))
  map_one' := by
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    exact map_one (algebraMap R (CompletedGroupAlgebraStageInClass C R G U))
  map_add' r s := by
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    exact map_add
      (algebraMap R (CompletedGroupAlgebraStageInClass C R G U)) r s
  map_mul' r s := by
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    exact map_mul
      (algebraMap R (CompletedGroupAlgebraStageInClass C R G U)) r s

/-- The \(C\)-indexed completed group algebra is an algebra over its coefficient ring. -/
instance instAlgebraCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) :
    Algebra R (CompletedGroupAlgebraInClass C R G) where
  algebraMap := completedGroupAlgebraAlgebraMapInClass
    (R := R) (G := G) C
  commutes' := by
    intro r x
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    exact Algebra.commutes r
      (completedGroupAlgebraProjectionInClass C R G U x)
  smul_def' := by
    intro r x
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    have hproj :
        completedGroupAlgebraProjectionInClass C R G U (r • x) =
          r • completedGroupAlgebraProjectionInClass C R G U x := by
      let _ : Module R
          (completedGroupAlgebraSystemInClass C R G).inverseLimit :=
        instModuleCoeffCompletedGroupAlgebraInClass (G := G) (R := R) C
      change
        (completedGroupAlgebraSystemInClass C R G).projection U
            (r • completedGroupAlgebraInClassCompatibleFamilyEquiv
              (R := R) (G := G) C x) =
          r • (completedGroupAlgebraSystemInClass C R G).projection U
            (completedGroupAlgebraInClassCompatibleFamilyEquiv
              (R := R) (G := G) C x)
      rfl
    calc
      completedGroupAlgebraProjectionInClass C R G U (r • x) =
          r • completedGroupAlgebraProjectionInClass C R G U x := hproj
      _ = algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r *
          completedGroupAlgebraProjectionInClass C R G U x :=
        Algebra.smul_def r (completedGroupAlgebraProjectionInClass C R G U x)
      _ = completedGroupAlgebraProjectionInClass C R G U
          (completedGroupAlgebraAlgebraMapInClass (R := R) (G := G) C r) *
            completedGroupAlgebraProjectionInClass C R G U x := by rfl
      _ = completedGroupAlgebraProjectionInClass C R G U
          (completedGroupAlgebraAlgebraMapInClass (R := R) (G := G) C r * x) :=
        (map_mul (completedGroupAlgebraProjectionInClass C R G U)
          (completedGroupAlgebraAlgebraMapInClass (R := R) (G := G) C r) x).symm

end

end CompletedGroupAlgebra
