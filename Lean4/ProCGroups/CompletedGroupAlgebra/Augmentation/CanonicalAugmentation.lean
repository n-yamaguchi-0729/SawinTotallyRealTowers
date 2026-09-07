import ProCGroups.CompletedGroupAlgebra.Augmentation.StageAugmentation

set_option autoImplicit false

/-!
# Canonical augmentation of the in-class completion

Compatible finite-stage augmentations assemble into the canonical augmentation of the in-class
completed group algebra. This file proves its projection, coefficient-map, continuity, and
surjectivity properties.
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

/-- The \(C\)-indexed completed augmentation evaluated at a finite stage. -/
def completedGroupAlgebraAugmentationAtInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraInClass C R G → R :=
  fun x => completedGroupAlgebraStageAugmentationInClass C R G U
    (completedGroupAlgebraProjectionInClass C R G U x)

/-- The augmentation value read at a finer in-class stage agrees after transition. -/
@[simp 900]
theorem completedGroupAlgebraAugmentationAtInClass_eq_of_le
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (x : CompletedGroupAlgebraInClass C R G) :
    completedGroupAlgebraAugmentationAtInClass C R G  U x =
      completedGroupAlgebraAugmentationAtInClass C R G  V x := by
  unfold completedGroupAlgebraAugmentationAtInClass
  have hcomp := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraStageAugmentationInClass_compatible
        (R := R) (G := G) C (U := U) (V := V) hUV))
    (completedGroupAlgebraProjectionInClass C R G V x)
  calc
    completedGroupAlgebraStageAugmentationInClass C R G U
        (completedGroupAlgebraProjectionInClass C R G U x)
        =
      completedGroupAlgebraStageAugmentationInClass C R G U
        (completedGroupAlgebraTransitionInClass C R G hUV
          (completedGroupAlgebraProjectionInClass C R G V x)) := by
          rw [← completedGroupAlgebraProjectionInClass_compatible
            (R := R) (G := G) C hUV x]
    _ =
      completedGroupAlgebraStageAugmentationInClass C R G V
        (completedGroupAlgebraProjectionInClass C R G V x) := hcomp

/-- The canonical augmentation on the \(C\)-indexed completed group algebra. -/
def completedGroupAlgebraCanonicalAugmentationInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    CompletedGroupAlgebraInClass C R G →+* R :=
  (completedGroupAlgebraStageAugmentationInClass C R G
    (terminalCompletedGroupAlgebraIndexInClass (G := G) C)).comp
      (completedGroupAlgebraProjectionInClass C R G
        (terminalCompletedGroupAlgebraIndexInClass (G := G) C))

/-- The in-class canonical augmentation can be computed at any in-class stage. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationInClass_eq_at
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (U : CompletedGroupAlgebraIndexInClass G C) (x : CompletedGroupAlgebraInClass C R G) :
    completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C x =
      completedGroupAlgebraAugmentationAtInClass C R G  U x :=
  completedGroupAlgebraAugmentationAtInClass_eq_of_le (R := R) (G := G) C
    (U := terminalCompletedGroupAlgebraIndexInClass (G := G) C) (V := U)
    (terminalCompletedGroupAlgebraIndexInClass_le (G := G) C U) x

/-- Stage augmentation after projection is the in-class canonical augmentation. -/
@[simp]
theorem completedGroupAlgebraStageAugmentationInClass_comp_projectionInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    (completedGroupAlgebraStageAugmentationInClass C R G U).comp
        (completedGroupAlgebraProjectionInClass C R G U) =
      completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C := by
  apply RingHom.ext
  intro x
  exact (completedGroupAlgebraCanonicalAugmentationInClass_eq_at
    (R := R) (G := G) C U x).symm

/--
The in-class canonical augmentation extends the abstract augmentation on the dense algebraic
map.
-/
@[simp]
theorem canonicalAugmentationInClass_toCompleted
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] (x : MonoidAlgebra R G) :
    completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C
        (toCompletedGroupAlgebraInClass C R G x) =
      groupAlgebraAugmentation R G x := by
  change completedGroupAlgebraStageAugmentationInClass C R G
      (terminalCompletedGroupAlgebraIndexInClass (G := G) C)
      (completedGroupAlgebraProjectionInClass C R G
        (terminalCompletedGroupAlgebraIndexInClass (G := G) C)
        (toCompletedGroupAlgebraInClass C R G x)) =
    groupAlgebraAugmentation R G x
  rw [completedGroupAlgebraProjectionInClass_toCompletedGroupAlgebraInClass]
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraStageAugmentationInClass_comp_stageMapInClass
        (R := R) (G := G) C (terminalCompletedGroupAlgebraIndexInClass (G := G) C)))
    x

/-- Composing the dense in-class map with canonical augmentation gives abstract augmentation. -/
@[simp]
theorem completedGACanonicalAugmentationInClass_comp_toCompletedGAInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C ).comp
        (toCompletedGroupAlgebraInClassRingHom C R G) =
      groupAlgebraAugmentation R G := by
  apply RingHom.ext
  intro x
  exact canonicalAugmentationInClass_toCompleted
    (R := R) (G := G) C x

/-- In-class canonical augmentation is natural in the coefficient ring. -/
@[simp 900]
theorem completedGroupAlgebraCanonicalAugmentationInClass_comp_coeffMapInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (S : Type w) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) :
    (completedGroupAlgebraCanonicalAugmentationInClass (R := S) (G := G) C ).comp
        (completedGroupAlgebraCoeffMapInClass (R := R) (G := G) C S f) =
      f.comp (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C ) := by
  apply RingHom.ext
  intro x
  let U := terminalCompletedGroupAlgebraIndexInClass (G := G) C
  change
    completedGroupAlgebraStageAugmentationInClass C S G U
        (completedGroupAlgebraProjectionInClass C S G U
          (completedGroupAlgebraCoeffMapInClass (R := R) (G := G) C S f x)) =
      f (completedGroupAlgebraStageAugmentationInClass C R G U
        (completedGroupAlgebraProjectionInClass C R G U x))
  rw [completedGroupAlgebraProjectionInClass_coeffMap]
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraStageAugmentationInClass_comp_stageCoeffMapInClass
        (R := R) (G := G) C S f U))
    (completedGroupAlgebraProjectionInClass C R G U x)

/-- The in-class canonical augmentation sends scalar algebra-map elements to their scalar. -/
@[simp 900]
theorem completedGroupAlgebraCanonicalAugmentationInClass_algebraMap
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] (r : R) :
    completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C
        (algebraMap R (CompletedGroupAlgebraInClass C R G) r) = r := by
  let U := terminalCompletedGroupAlgebraIndexInClass (G := G) C
  calc
    completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C
        (algebraMap R (CompletedGroupAlgebraInClass C R G) r)
        =
      completedGroupAlgebraStageAugmentationInClass C R G U
        (completedGroupAlgebraProjectionInClass C R G U
          (algebraMap R (CompletedGroupAlgebraInClass C R G) r)) := rfl
    _ =
      completedGroupAlgebraStageAugmentationInClass C R G U
        (algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r) := by
          change completedGroupAlgebraStageAugmentationInClass C R G U
              (completedGroupAlgebraProjectionInClass C R G U
                (completedGroupAlgebraAlgebraMapInClass (R := R) (G := G) C r)) =
            completedGroupAlgebraStageAugmentationInClass C R G U
              (algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r)
          exact congrArg (completedGroupAlgebraStageAugmentationInClass C R G U)
            (completedGroupAlgebraProjectionInClass_algebraMap
              (R := R) (G := G) C U r)
    _ = r := by
      simp only [completedGroupAlgebraStageAugmentationInClass, MonoidAlgebra.coe_algebraMap,
  Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq,
      groupAlgebraAugmentation_single]

/--
The \(C\)-indexed canonical augmentation \(\varepsilon_C:\widehat{R[G]}_C\to R\) is surjective.
-/
theorem completedGroupAlgebraCanonicalAugmentationInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Function.Surjective
      (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C ) := by
  intro r
  refine ⟨algebraMap R (CompletedGroupAlgebraInClass C R G) r, ?_⟩
  simp only [completedGroupAlgebraCanonicalAugmentationInClass_algebraMap]

/--
The \(C\)-indexed canonical augmentation is continuous for the inverse-limit topology on
\(\widehat{R[G]}_C\).
-/
theorem continuous_completedGroupAlgebraCanonicalAugmentationInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Continuous (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C ) := by
  let U := terminalCompletedGroupAlgebraIndexInClass (G := G) C
  let : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
    finite_completedGroupAlgebraQuotientInClass G C U
  let : TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    (completedGroupAlgebraSystemInClass C R G).topologicalSpace U
  change Continuous fun x : CompletedGroupAlgebraInClass C R G =>
    completedGroupAlgebraStageAugmentationInClass C R G U
      (completedGroupAlgebraProjectionInClass C R G U x)
  exact (finiteGroupAlgebra_augmentation_continuous R
    (CompletedGroupAlgebraQuotientInClass G C U)).comp
      ((completedGroupAlgebraSystemInClass C R G).continuous_projection U)

/--
The \(C\)-indexed completed group algebra carries the standard model-independent augmentation
package.
-/
theorem completedGroupAlgebraInClass_hasCompletedGroupAlgebraAugmentation
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    hasCompletedGroupAlgebraAugmentation R G (CompletedGroupAlgebraInClass C R G)
      (toCompletedGroupAlgebraInClassRingHom C R G) := by
  refine ⟨completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C , ?_, ?_⟩
  · exact completedGACanonicalAugmentationInClass_comp_toCompletedGAInClass
      (R := R) (G := G) C
  · exact continuous_completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C

end

end CompletedGroupAlgebra
