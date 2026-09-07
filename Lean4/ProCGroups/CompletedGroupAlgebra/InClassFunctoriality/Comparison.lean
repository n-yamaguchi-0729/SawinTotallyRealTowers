import ProCGroups.CompletedGroupAlgebra.InClassFunctoriality.GroupLike
import ProCGroups.CompletedGroupAlgebra.UniversalProperty.Basic

set_option autoImplicit false

/-!
# Comparison maps for in-class completions

This file computes the canonical maps between all-finite and in-class completed group algebras on
group-like elements and their differences from one. It also records the corresponding formulas
for functorial maps and restricted scalar actions.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The all-finite completed group algebra comparison sends group-like elements to the \(C\)-indexed
group-like elements.
-/
@[simp]
theorem completedGroupAlgebraToInClass_of
    (C : ProCGroups.FiniteGroupClass.{v})
    (g : G) :
    completedGroupAlgebraToInClassRingHom (R := R) (G := G) C
        (completedGroupAlgebraOf R G g) =
      completedGroupAlgebraOfInClass C R G g := by
  change ((completedGroupAlgebraToInClassRingHom (R := R) (G := G) C ).comp
      (toCompletedGroupAlgebraRingHom R G)) (MonoidAlgebra.of R G g) =
    toCompletedGroupAlgebraInClassRingHom C R G (MonoidAlgebra.of R G g)
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraToInClass_comp_toCompletedGroupAlgebra
        (R := R) (G := G) C ))
    (MonoidAlgebra.of R G g)

/--
The comparison map to a class-indexed completion sends all-finite augmentation generators to
class-indexed generators.
-/
@[simp]
theorem completedGroupAlgebraToInClass_of_sub_one
    (C : ProCGroups.FiniteGroupClass.{v})
    (g : G) :
    completedGroupAlgebraToInClassRingHom (R := R) (G := G) C
        (completedGroupAlgebraOf R G g - 1) =
      completedGroupAlgebraOfInClass C R G g - 1 := by
  rw [map_sub, completedGroupAlgebraToInClass_of, map_one]

/--
After restricting scalars along \(\widehat{R[G]} \to \widehat{R[G]}_C\), the all-finite
augmentation generator acts as the matching \(C\)-indexed generator.
-/
@[simp]
theorem completedGroupAlgebraToInClass_restrictScalars_sub_one_smul
    (C : ProCGroups.FiniteGroupClass.{v})
    (A : Type w) [AddCommGroup A] [Module (CompletedGroupAlgebraInClass C R G) A]
    (g : G) (a : A) :
    letI : Module (CompletedGroupAlgebraCarrier R G) A :=
      Module.compHom A (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C )
    (completedGroupAlgebraOf R G g - 1) • a =
      (completedGroupAlgebraOfInClass C R G g - 1) • a := by
  exact congrArg (fun z : CompletedGroupAlgebraInClass C R G => z • a)
    (completedGroupAlgebraToInClass_of_sub_one (R := R) (G := G) C g)

/--
The comparison map from a class-indexed completion sends class-indexed group-like elements to
all-finite group-like elements.
-/
@[simp]
theorem completedGroupAlgebraFromInClass_of
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) (g : G) :
    completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG
        (completedGroupAlgebraOfInClass C R G g) =
      completedGroupAlgebraOf R G g := by
  change ((completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG).comp
      (toCompletedGroupAlgebraInClassRingHom C R G)) (MonoidAlgebra.of R G g) =
    toCompletedGroupAlgebraRingHom R G (MonoidAlgebra.of R G g)
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraFromInClassRingHom_comp_toCompletedGroupAlgebraInClass
        (R := R) (G := G) C hForm hG))
    (MonoidAlgebra.of R G g)

/--
The comparison map from a class-indexed completion sends class-indexed augmentation generators
to all-finite generators.
-/
@[simp]
theorem completedGroupAlgebraFromInClass_of_sub_one
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) (g : G) :
    completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG
        (completedGroupAlgebraOfInClass C R G g - 1) =
      completedGroupAlgebraOf R G g - 1 := by
  change completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG
      (completedGroupAlgebraOfInClass C R G g - 1) =
    completedGroupAlgebraOf R G g - 1
  rw [map_sub, map_one]
  change completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG
      (completedGroupAlgebraOfInClass C R G g) - 1 =
    completedGroupAlgebraOf R G g - 1
  rw [completedGroupAlgebraFromInClass_of]

/--
After restricting scalars along \(\widehat{R[G]}_C \to \widehat{R[G]}\), the \(C\)-indexed
augmentation generator acts as the matching all-finite generator.
-/
@[simp]
theorem completedGroupAlgebraFromInClass_restrictScalars_sub_one_smul
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G)
    (A : Type w) [AddCommGroup A] [Module (CompletedGroupAlgebraCarrier R G) A]
    (g : G) (a : A) :
    letI : Module (CompletedGroupAlgebraInClass C R G) A :=
      Module.compHom A (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG)
    (completedGroupAlgebraOfInClass C R G g - 1) • a =
      (completedGroupAlgebraOf R G g - 1) • a := by
  exact congrArg (fun z : CompletedGroupAlgebraCarrier R G => z • a)
    (completedGroupAlgebraFromInClass_of_sub_one (R := R) (G := G) C hForm hG g)

/--
The class-indexed completed group-algebra map sends the completed group-like element of \(g\) to
the completed group-like element of its image.
-/
@[simp]
theorem completedGroupAlgebraMapInClass_of
    (C : ProCGroups.FiniteGroupClass.{v})
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (g : G) :
    completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ
        (completedGroupAlgebraOfInClass C R G g) =
      completedGroupAlgebraOfInClass C R H (φ g) := by
  simpa [completedGroupAlgebraOfInClass] using
    completedGroupAlgebraMapInClass_toCompletedGroupAlgebraInClass_of
      (R := R) (G := G) (H := H) C hHer φ hφ g

/-- The class-indexed functorial map sends group-like augmentation generators to their images. -/
@[simp]
theorem completedGroupAlgebraMapInClass_of_sub_one
    (C : ProCGroups.FiniteGroupClass.{v})
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (g : G) :
    completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ
        (completedGroupAlgebraOfInClass C R G g - 1) =
      completedGroupAlgebraOfInClass C R H (φ g) - 1 := by
  rw [map_sub, completedGroupAlgebraMapInClass_of, map_one]

end

end CompletedGroupAlgebra
