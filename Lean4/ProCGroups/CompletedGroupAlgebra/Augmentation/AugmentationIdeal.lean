import ProCGroups.CompletedGroupAlgebra.Augmentation.CanonicalAugmentation

set_option autoImplicit false

/-!
# The in-class augmentation ideal

This file defines the kernel of the canonical augmentation on the in-class completed group
algebra, establishes the associated short exact sequence, and identifies the ideal through the
canonical map from the algebraic group algebra.
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

/-- The canonical augmentation ideal of the \(C\)-indexed completed group algebra. -/
def completedGroupAlgebraCanonicalAugmentationIdealInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Ideal (CompletedGroupAlgebraInClass C R G) :=
  RingHom.ker (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C )

/--
An in-class completed group-algebra element lies in the canonical augmentation ideal iff the
in-class canonical augmentation sends it to zero.
-/
@[simp]
theorem mem_completedGroupAlgebraCanonicalAugmentationIdealInClass_iff
    {R : Type u} {G : Type v} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {C : ProCGroups.FiniteGroupClass.{v}}
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    {x : CompletedGroupAlgebraInClass C R G} :
    x ∈ completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C ↔
      completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C x = 0 :=
  Iff.rfl

/-- The inclusion of the \(C\)-indexed canonical augmentation ideal is injective. -/
theorem completedGroupAlgebraCanonicalAugmentationIdealInClass_subtype_injective
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Function.Injective
      (fun x : completedGroupAlgebraCanonicalAugmentationIdealInClass
          (R := R) (G := G) C => (x : CompletedGroupAlgebraInClass C R G)) := by
  intro x y hxy
  exact Subtype.ext hxy

/--
The \(C\)-indexed canonical augmentation ideal is exactly the kernel of the canonical
augmentation.
-/
theorem exact_completedGroupAlgebraCanonicalAugmentationIdealInClass_subtype
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Function.Exact
      (fun x : completedGroupAlgebraCanonicalAugmentationIdealInClass
          (R := R) (G := G) C => (x : CompletedGroupAlgebraInClass C R G))
      (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C ) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2

/--
The canonical augmentation sequence with augmentation ideal as kernel is short exact: the
inclusion is injective, its image is the kernel of augmentation, and the augmentation is
surjective.
-/
theorem completedGroupAlgebraCanonicalAugmentationInClass_shortExact
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Function.Injective
        (fun x : completedGroupAlgebraCanonicalAugmentationIdealInClass
          (R := R) (G := G) C => (x : CompletedGroupAlgebraInClass C R G)) ∧
      Function.Exact
        (fun x : completedGroupAlgebraCanonicalAugmentationIdealInClass
          (R := R) (G := G) C => (x : CompletedGroupAlgebraInClass C R G))
        (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C ) ∧
      Function.Surjective
        (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C ) := by
  exact ⟨completedGroupAlgebraCanonicalAugmentationIdealInClass_subtype_injective
      (R := R) (G := G) C ,
    exact_completedGroupAlgebraCanonicalAugmentationIdealInClass_subtype
      (R := R) (G := G) C ,
    completedGroupAlgebraCanonicalAugmentationInClass_surjective (R := R) (G := G) C ⟩

/-- The in-class canonical augmentation sends every completed group-like element to one. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationInClass_of
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] (g : G) :
    completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C
        (completedGroupAlgebraOfInClass C R G g) = 1 := by
  rw [completedGroupAlgebraOfInClass,
    canonicalAugmentationInClass_toCompleted]
  simp only [MonoidAlgebra.of_apply, groupAlgebraAugmentation_single]

end

end CompletedGroupAlgebra
