import ProCGroups.CompletedGroupAlgebra.Basic.InClass.Stage

set_option autoImplicit false

/-!
# Completed Group Algebra / Basic / Within a Class / System

This module assembles the \(C\)-indexed stages into a topological inverse system and supplies the
single `IsRingSystem` witness from which the completed carrier inherits its ring structure.
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


/--
The \(C\)-indexed inverse system \(U\mapsto R[G/U]\). The hypothesis says that \(C\) really is a
finite quotient class, so every stage carries the finite-product topology.
-/
def completedGroupAlgebraSystemInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ProCGroups.InverseSystems.InverseSystem (I := CompletedGroupAlgebraIndexInClass G C) where
  X := CompletedGroupAlgebraStageInClass C R G
  topologicalSpace := fun U => by
    letI : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
      finite_completedGroupAlgebraQuotientInClass G C U
    exact finiteGroupAlgebraTopology R (CompletedGroupAlgebraQuotientInClass G C U)
  map := fun {U V} hUV => completedGroupAlgebraTransitionInClass C R G hUV
  continuous_map := by
    intro U V hUV
    let : Finite (CompletedGroupAlgebraQuotientInClass G C V) :=
      finite_completedGroupAlgebraQuotientInClass G C V
    let : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
      finite_completedGroupAlgebraQuotientInClass G C U
    exact finiteGroupAlgebra_mapDomainRingHom_continuous R
      (CompletedGroupAlgebraQuotientInClass G C V) (CompletedGroupAlgebraQuotientInClass G C U)
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
  map_id := by
    intro U
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraTransitionInClass_id (R := R) (G := G) C U)) x
  map_comp := by
    intro U V W hUV hVW
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraTransitionInClass_comp (R := R) (G := G) C hUV hVW)) x

local instance
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) :
    Ring ((completedGroupAlgebraSystemInClass C R G).X U) := by
  change Ring (CompletedGroupAlgebraStageInClass C R G U)
  infer_instance

/--
The inverse system of finite-stage group algebras inherits a ring structure from the compatible
finite-stage rings.
-/
instance instIsRingSystemCompletedGroupAlgebraSystemInClass
    (C : ProCGroups.FiniteGroupClass.{v}) :
    IsRingSystem (completedGroupAlgebraSystemInClass C R G) where
  map_zero := by
    intro U V hUV
    exact map_zero (completedGroupAlgebraTransitionInClass C R G hUV)
  map_one := by
    intro U V hUV
    exact map_one (completedGroupAlgebraTransitionInClass C R G hUV)
  map_add := by
    intro U V hUV x y
    exact map_add (completedGroupAlgebraTransitionInClass C R G hUV) x y
  map_mul := by
    intro U V hUV x y
    exact map_mul (completedGroupAlgebraTransitionInClass C R G hUV) x y


end

end CompletedGroupAlgebra
