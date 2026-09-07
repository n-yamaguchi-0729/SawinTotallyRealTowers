import ProCGroups.CompletedGroupAlgebra.InClassFunctoriality.Maps

set_option autoImplicit false

/-!
# Completed Group Algebra / Functoriality Within a Class / Group-Like

This module constructs the \(C\)-indexed completed group-like map through the canonical dense map,
and characterizes it by finite-stage projections, multiplication, and continuity.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A group element maps to its image in the \(C\)-indexed completed group algebra. -/
def completedGroupAlgebraOfInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (g : G) : CompletedGroupAlgebraInClass C R G :=
  toCompletedGroupAlgebraInClass C R G (MonoidAlgebra.of R G g)

/-- Projection of a class-indexed completed group-like element to a finite quotient stage. -/
@[simp]
theorem completedGroupAlgebraProjectionInClass_of
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) (g : G) :
    completedGroupAlgebraProjectionInClass C R G U
        (completedGroupAlgebraOfInClass C R G g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U g) 1 := by
  rw [completedGroupAlgebraOfInClass,
    completedGroupAlgebraProjectionInClass_toCompletedGroupAlgebraInClass,
    completedGroupAlgebraStageMapInClass_of]

/-- The class-indexed completed group-like element attached to one is the unit. -/
@[simp]
theorem completedGroupAlgebraOfInClass_one
    (C : ProCGroups.FiniteGroupClass.{v}) :
    completedGroupAlgebraOfInClass C R G 1 =
      (1 : CompletedGroupAlgebraInClass C R G) := by
  apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
  intro U
  rw [completedGroupAlgebraProjectionInClass_of]
  change MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U 1)
      (1 : R) =
    completedGroupAlgebraProjectionInClass C R G U
      (1 : CompletedGroupAlgebraInClass C R G)
  rw [map_one]
  change MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U 1)
      (1 : R) = 1
  rfl

/-- Class-indexed completed group-like elements multiply according to the group law. -/
@[simp 900]
theorem completedGroupAlgebraOfInClass_mul
    (C : ProCGroups.FiniteGroupClass.{v})
    (g h : G) :
    completedGroupAlgebraOfInClass C R G (g * h) =
      completedGroupAlgebraOfInClass C R G g *
        completedGroupAlgebraOfInClass C R G h := by
  change toCompletedGroupAlgebraInClass C R G (MonoidAlgebra.of R G (g * h)) =
    toCompletedGroupAlgebraInClass C R G (MonoidAlgebra.of R G g) *
      toCompletedGroupAlgebraInClass C R G (MonoidAlgebra.of R G h)
  rw [map_mul (MonoidAlgebra.of R G) g h]
  have happ (x : MonoidAlgebra R G) :
      toCompletedGroupAlgebraInClassRingHom C R G x =
        toCompletedGroupAlgebraInClass C R G x := rfl
  have hmul := map_mul (toCompletedGroupAlgebraInClassRingHom C R G)
    (MonoidAlgebra.of R G g) (MonoidAlgebra.of R G h)
  rw [happ, happ, happ] at hmul
  exact hmul

/-- The class-indexed finite-stage group-like map is continuous. -/
theorem continuous_completedGroupAlgebraStageMapInClass_of
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) :
    letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
      (completedGroupAlgebraSystemInClass C R G).topologicalSpace U
    Continuous fun g : G => completedGroupAlgebraStageMapInClass C R G U
      (MonoidAlgebra.of R G g) := by
  let : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
    finite_completedGroupAlgebraQuotientInClass G C U
  let : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    (completedGroupAlgebraSystemInClass C R G).topologicalSpace U
  let : DiscreteTopology (CompletedGroupAlgebraQuotientInClass G C U) :=
    QuotientGroup.discreteTopology
      (ProCGroups.openNormalSubgroup_isOpen (G := G) ((OrderDual.ofDual U).1 :
          OpenNormalSubgroup G))
  have hbasis :
      @Continuous (CompletedGroupAlgebraQuotientInClass G C U)
        (CompletedGroupAlgebraStageInClass C R G U) inferInstance
        ((completedGroupAlgebraSystemInClass C R G).topologicalSpace U)
        (fun q => MonoidAlgebra.single q (1 : R)) :=
    continuous_of_discreteTopology
  have hproj :
      Continuous fun g : G => openNormalSubgroupInClassProj (C := C) (G := G) U g := by
    change Continuous
      (QuotientGroup.mk' (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G))
    exact continuous_quotient_mk'
  have hcont := hbasis.comp hproj
  change @Continuous G (CompletedGroupAlgebraStageInClass C R G U) (‹TopologicalSpace G›)
    ((completedGroupAlgebraSystemInClass C R G).topologicalSpace U)
    (fun g => MonoidAlgebra.single
      (openNormalSubgroupInClassProj (C := C) (G := G) U g) (1 : R)) at hcont
  convert hcont using 1
  funext g
  exact completedGroupAlgebraStageMapInClass_of (R := R) (G := G) C U g

/-- The class-indexed completed group-like map is continuous. -/
theorem continuous_completedGroupAlgebraOfInClass
    (C : ProCGroups.FiniteGroupClass.{v}) :
    Continuous (completedGroupAlgebraOfInClass C R G) := by
  let S := completedGroupAlgebraSystemInClass C R G
  let : ∀ U, TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    fun U => (completedGroupAlgebraSystemInClass C R G).topologicalSpace U
  let π : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      G → CompletedGroupAlgebraStageInClass C R G U :=
    fun U g =>
      completedGroupAlgebraStageMapInClass C R G U
        (MonoidAlgebra.of R G g)
  have hπ : ∀ U, Continuous (π U) := by
    intro U
    exact continuous_completedGroupAlgebraStageMapInClass_of
      (R := R) (G := G) C U
  have hcompat : S.CompatibleMaps π := by
    intro U V hUV
    funext g
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraStageMapInClass_compatible
          (R := R) (G := G) C hUV))
      (MonoidAlgebra.of R G g)
  change Continuous (S.inverseLimitLift π hcompat)
  exact S.continuous_inverseLimitLift π hπ hcompat

end

end CompletedGroupAlgebra
