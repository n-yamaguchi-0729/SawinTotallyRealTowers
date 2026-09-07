import ProCGroups.CompletedGroupAlgebra.AllFiniteAugmentation.CanonicalAugmentation
import ProCGroups.CompletedGroupAlgebra.Augmentation.CanonicalAugmentation

set_option autoImplicit false

/-!
# Comparing all-finite and in-class augmentations

The canonical comparison maps between the all-finite and in-class completions commute with their
augmentations. This file records both directions of that compatibility.
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
Composing the class-indexed canonical augmentation with the comparison map gives the all-finite
augmentation.
-/
@[simp 900]
theorem completedGroupAlgebraCanonicalAugmentationInClass_comp_toInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C ).comp
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C ) =
      completedGroupAlgebraCanonicalAugmentation R G := by
  apply RingHom.ext
  intro x
  let Uc : CompletedGroupAlgebraIndexInClass G C :=
    terminalCompletedGroupAlgebraIndexInClass (G := G) C
  let U : CompletedGroupAlgebraIndex G :=
    completedGroupAlgebraIndexInClassToAllFinite G C Uc
  calc
    completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C x)
        =
      completedGroupAlgebraAugmentationAtInClass C R G  Uc
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C x) := by
          exact completedGroupAlgebraCanonicalAugmentationInClass_eq_at
            (R := R) (G := G) C Uc
            (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C x)
    _ =
      completedGroupAlgebraStageAugmentationInClass C R G Uc
        (completedGroupAlgebraProjectionToStageInClass (R := R) (G := G) C Uc x) := rfl
    _ =
      completedGroupAlgebraStageAugmentation R G U
        (completedGroupAlgebraProjection R G U x) := rfl
    _ = completedGroupAlgebraCanonicalAugmentation R G x := by
      exact (completedGroupAlgebraCanonicalAugmentation_eq_at (R := R) (G := G) U x).symm

/--
The all-finite canonical augmentation after the comparison map from a class-indexed completion
agrees with the class-indexed augmentation.
-/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_fromInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G)
    (x : CompletedGroupAlgebraInClass C R G) :
    completedGroupAlgebraCanonicalAugmentation R G
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x) =
      completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C x := by
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraCanonicalAugmentationInClass_comp_toInClass
        (R := R) (G := G) C ))
    (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x)
  change completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C
      (completedGroupAlgebraToInClass (R := R) (G := G) C
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x)) =
    completedGroupAlgebraCanonicalAugmentation R G
      (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x) at h
  rw [completedGroupAlgebraToInClass_fromInClass] at h
  exact h.symm
end

end CompletedGroupAlgebra
