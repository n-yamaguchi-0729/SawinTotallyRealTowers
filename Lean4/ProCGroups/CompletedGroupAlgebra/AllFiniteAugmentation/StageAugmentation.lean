import ProCGroups.CompletedGroupAlgebra.AllFiniteAugmentation.TerminalIndex

set_option autoImplicit false

/-!
# Augmentation at all-finite quotient stages

This file defines augmentation on each finite coefficient-and-group stage of the all-finite
system and proves its formulas on basis elements and compatibility with transition, coefficient,
and functorial stage maps.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The augmentation map on a finite stage is the ring homomorphism \(R[G/U]\to R\) that sends every
group-like basis element to \(1\).
-/
def completedGroupAlgebraStageAugmentation (R : Type u) (G : Type v) [CommRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndex G) :
    CompletedGroupAlgebraStage R G U →+* R :=
  groupAlgebraAugmentation R (CompletedGroupAlgebraQuotient G U)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The finite-stage augmentation sends every group-like basis element to one. -/
@[simp]
theorem completedGroupAlgebraStageAugmentation_of
    (U : CompletedGroupAlgebraIndex G) (q : CompletedGroupAlgebraQuotient G U) :
    completedGroupAlgebraStageAugmentation R G U (MonoidAlgebra.of R _ q) = 1 := by
  simp only [completedGroupAlgebraStageAugmentation, MonoidAlgebra.of_apply,
      groupAlgebraAugmentation_single]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The finite-stage augmentation sends a singleton to its coefficient. -/
@[simp]
theorem completedGroupAlgebraStageAugmentation_single
    (U : CompletedGroupAlgebraIndex G) (q : CompletedGroupAlgebraQuotient G U) (r : R) :
    completedGroupAlgebraStageAugmentation R G U (MonoidAlgebra.single q r) = r := by
  simp only [completedGroupAlgebraStageAugmentation, groupAlgebraAugmentation_single]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Finite-stage augmentations are compatible with transition maps. -/
@[simp]
theorem completedGroupAlgebraStageAugmentation_compatible
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (completedGroupAlgebraStageAugmentation R G U).comp
        (completedGroupAlgebraTransition R G hUV) =
      completedGroupAlgebraStageAugmentation R G V := by
  apply RingHom.ext
  intro x
  exact groupAlgebraAugmentation_mapDomainRingHom R
    (CompletedGroupAlgebraQuotient G V) (CompletedGroupAlgebraQuotient G U)
    (OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) x

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Finite-stage augmentation after the stage map is the abstract group-algebra augmentation. -/
@[simp]
theorem completedGroupAlgebraStageAugmentation_comp_stageMap
    (U : CompletedGroupAlgebraIndex G) :
    (completedGroupAlgebraStageAugmentation R G U).comp
        (completedGroupAlgebraStageMap R G U) =
      groupAlgebraAugmentation R G := by
  apply RingHom.ext
  intro x
  exact groupAlgebraAugmentation_mapDomainRingHom R G (CompletedGroupAlgebraQuotient G U)
    (openNormalSubgroupInClassProj
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U) x

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Finite-stage augmentation is natural in the coefficient ring. -/
@[simp]
theorem completedGroupAlgebraStageAugmentation_comp_stageCoeffMap
    (S : Type w) [CommRing S] (f : R →+* S) (U : CompletedGroupAlgebraIndex G) :
    (completedGroupAlgebraStageAugmentation S G U).comp
        (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U) =
      f.comp (completedGroupAlgebraStageAugmentation R G U) := by
  apply RingHom.ext
  intro x
  exact groupAlgebraAugmentation_mapRangeRingHom R S
    (CompletedGroupAlgebraQuotient G U) f x

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Finite-stage augmentation is natural with respect to functorial finite-stage maps. -/
@[simp]
theorem completedGroupAlgebraStageAugmentation_comp_functorialStageMap
    (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) :
    (completedGroupAlgebraStageAugmentation R H V).comp
        (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) φ hφ V) =
      completedGroupAlgebraStageAugmentation R G
        (completedGroupAlgebraComapIndex (G := G) φ hφ V) := by
  apply RingHom.ext
  intro x
  exact groupAlgebraAugmentation_mapDomainRingHom R
    (CompletedGroupAlgebraQuotient G (completedGroupAlgebraComapIndex (G := G) φ hφ V))
    (CompletedGroupAlgebraQuotient H V)
    (completedGroupAlgebraComapQuotientMap (G := G) φ hφ V) x
end

end CompletedGroupAlgebra
