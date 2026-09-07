import ProCGroups.CompletedGroupAlgebra.Basic.InClass.LimitAlgebra

set_option autoImplicit false

/-!
# Completed Group Algebra / Basic / Within a Class / Projection

This module bundles the canonical \(C\)-indexed finite-stage projection as ring, algebra, linear,
and continuous linear maps. The underlying projection and compatibility theorem are defined with
the opaque carrier in `LimitAlgebra`.
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


/-- Projection of a coefficient element to a finite stage is the stage algebra map. -/
@[simp]
theorem completedGroupAlgebraProjectionInClass_algebraMap
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) (r : R) :
    completedGroupAlgebraProjectionInClass C R G U
        (completedGroupAlgebraAlgebraMapInClass (R := R) (G := G) C r) =
      algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r :=
  rfl

/-- Projection of a coefficient-changed element is coefficient change of the projection. -/
@[simp]
theorem completedGroupAlgebraProjectionInClass_coeffMap
    (C : ProCGroups.FiniteGroupClass.{v})
    (S : Type w) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) (U : CompletedGroupAlgebraIndexInClass G C)
    (x : CompletedGroupAlgebraInClass C R G) :
    completedGroupAlgebraProjectionInClass C S G U
        (completedGroupAlgebraCoeffMapInClass (R := R) (G := G) C S f x) =
      completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U
        (completedGroupAlgebraProjectionInClass C R G U x) :=
  rfl

/--
The projection from a \(C\)-indexed completed group algebra to a finite stage is bundled as an
algebra homomorphism.
-/
def completedGroupAlgebraProjectionAlgHomInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraInClass C R G →ₐ[R] CompletedGroupAlgebraStageInClass C R G U where
  toRingHom := completedGroupAlgebraProjectionInClass C R G U
  commutes' := by
    intro r
    rfl

/-- The projection from a \(C\)-indexed completed group algebra to a finite stage, viewed as an
\(R\)-linear map. -/
def completedGroupAlgebraProjectionLinearMapInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraInClass C R G →ₗ[R] CompletedGroupAlgebraStageInClass C R G U :=
  (completedGroupAlgebraProjectionAlgHomInClass C R G U).toLinearMap

/-- Composing a stage projection with a transition map gives the coarser stage projection. -/
@[simp]
theorem completedGroupAlgebraTransitionInClass_comp_projection
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (completedGroupAlgebraTransitionInClass C R G hUV).comp
        (completedGroupAlgebraProjectionInClass C R G V) =
      completedGroupAlgebraProjectionInClass C R G U := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraProjectionInClass_compatible (R := R) (G := G) C hUV x

/-- Continuity of the projection from the \(C\)-indexed completed group algebra to a stage. -/
theorem continuous_completedGroupAlgebraProjectionInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) :
    letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
      (completedGroupAlgebraSystemInClass C R G).topologicalSpace U
    Continuous (completedGroupAlgebraProjectionInClass C R G U) := by
  let : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    (completedGroupAlgebraSystemInClass C R G).topologicalSpace U
  exact (completedGroupAlgebraSystemInClass C R G).continuous_projection U

/--
The projection from a \(C\)-indexed completed group algebra to a finite stage is bundled as a
continuous \(R\)-linear map.
-/
def completedGroupAlgebraProjectionContinuousLinearMapInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
      (completedGroupAlgebraSystemInClass C R G).topologicalSpace U
    CompletedGroupAlgebraInClass C R G →L[R] CompletedGroupAlgebraStageInClass C R G U := by
  letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    (completedGroupAlgebraSystemInClass C R G).topologicalSpace U
  exact
    { toLinearMap := completedGroupAlgebraProjectionLinearMapInClass C R G U
      cont := (completedGroupAlgebraSystemInClass C R G).continuous_projection U }

end

end CompletedGroupAlgebra
