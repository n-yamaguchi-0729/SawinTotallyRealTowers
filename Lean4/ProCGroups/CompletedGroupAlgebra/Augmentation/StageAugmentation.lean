import ProCGroups.CompletedGroupAlgebra.InClassFunctoriality.UnitRepresentation

set_option autoImplicit false

/-!
# Augmentation at in-class quotient stages

This file defines augmentation on each in-class finite stage and proves its values on basis
elements and compatibility with transition, coefficient-change, and functorial stage maps.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (R : Type u) [CommRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The augmentation map on one \(C\)-indexed finite stage. -/
def completedGroupAlgebraStageAugmentationInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (R : Type u) (G : Type v) [CommRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraStageInClass C R G U →+* R :=
  groupAlgebraAugmentation R (CompletedGroupAlgebraQuotientInClass G C U)

/-- The in-class finite-stage augmentation sends every group-like basis element to one. -/
@[simp]
theorem completedGroupAlgebraStageAugmentationInClass_of
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (q : CompletedGroupAlgebraQuotientInClass G C U) :
    completedGroupAlgebraStageAugmentationInClass C R G U (MonoidAlgebra.of R _ q) = 1 := by
  simp only [completedGroupAlgebraStageAugmentationInClass, MonoidAlgebra.of_apply,
  groupAlgebraAugmentation_single]

/-- The in-class finite-stage augmentation sends a singleton to its coefficient. -/
@[simp]
theorem completedGroupAlgebraStageAugmentationInClass_single
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (q : CompletedGroupAlgebraQuotientInClass G C U) (r : R) :
    completedGroupAlgebraStageAugmentationInClass C R G U (MonoidAlgebra.single q r) = r := by
  simp only [completedGroupAlgebraStageAugmentationInClass, groupAlgebraAugmentation_single]

/-- In-class finite-stage augmentations are compatible with transition maps. -/
@[simp]
theorem completedGroupAlgebraStageAugmentationInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (completedGroupAlgebraStageAugmentationInClass C R G U).comp
        (completedGroupAlgebraTransitionInClass C R G hUV) =
      completedGroupAlgebraStageAugmentationInClass C R G V := by
  apply RingHom.ext
  intro x
  exact groupAlgebraAugmentation_mapDomainRingHom R
    (CompletedGroupAlgebraQuotientInClass G C V)
    (CompletedGroupAlgebraQuotientInClass G C U)
    (OpenNormalSubgroupInClass.map
      (C := C) (G := G) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) x

/--
Composing the in-class finite-stage augmentation with the stage map gives the abstract
augmentation.
-/
@[simp]
theorem completedGroupAlgebraStageAugmentationInClass_comp_stageMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C) :
    (completedGroupAlgebraStageAugmentationInClass C R G U).comp
        (completedGroupAlgebraStageMapInClass C R G U) =
      groupAlgebraAugmentation R G := by
  apply RingHom.ext
  intro x
  exact groupAlgebraAugmentation_mapDomainRingHom R G
    (CompletedGroupAlgebraQuotientInClass G C U)
    (openNormalSubgroupInClassProj (C := C) (G := G) U) x

/-- In-class finite-stage augmentation is natural in the coefficient ring. -/
@[simp]
theorem completedGroupAlgebraStageAugmentationInClass_comp_stageCoeffMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (S : Type w) [CommRing S]
    (f : R →+* S) (U : CompletedGroupAlgebraIndexInClass G C) :
    (completedGroupAlgebraStageAugmentationInClass C S G U).comp
        (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U) =
      f.comp (completedGroupAlgebraStageAugmentationInClass C R G U) := by
  apply RingHom.ext
  intro x
  exact groupAlgebraAugmentation_mapRangeRingHom R S
    (CompletedGroupAlgebraQuotientInClass G C U) f x

/-- In-class finite-stage augmentation is natural for functorial finite-stage maps. -/
@[simp]
theorem completedGroupAlgebraStageAugmentationInClass_comp_functorialStageMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (V : CompletedGroupAlgebraIndexInClass H C) :
    (completedGroupAlgebraStageAugmentationInClass C R H V).comp
        (completedGroupAlgebraFunctorialStageMapInClass
          (G := G) (H := H) C hHer (R := R) φ hφ V) =
      completedGroupAlgebraStageAugmentationInClass C R G
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) := by
  apply RingHom.ext
  intro x
  exact groupAlgebraAugmentation_mapDomainRingHom R
    (CompletedGroupAlgebraQuotientInClass G C
      (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V))
    (CompletedGroupAlgebraQuotientInClass H C V)
    (completedGroupAlgebraComapQuotientMapInClass (G := G) (H := H) C hHer φ hφ V) x

end

end CompletedGroupAlgebra
