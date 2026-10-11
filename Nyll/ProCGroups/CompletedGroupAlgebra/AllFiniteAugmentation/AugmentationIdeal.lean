/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CompletedGroupAlgebra.AllFiniteAugmentation.InClassComparison
import Nyll.ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.Surjectivity
import Nyll.ProCGroups.CompletedGroupAlgebra.Augmentation.AugmentationIdeal

/-!
# The canonical augmentation ideal

This file defines the kernel of the canonical augmentation on the all-finite completed group
algebra, packages its short exact sequence, and proves comparison and functoriality formulas for
the ideal.
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
The canonical augmentation ideal \(I_G\subseteq \widehat{R[G]}\) is the kernel of the completed
augmentation \(\varepsilon:\widehat{R[G]}\to R\).
-/
def completedGroupAlgebraCanonicalAugmentationIdeal (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Ideal (CompletedGroupAlgebraCarrier R G) :=
  RingHom.ker (completedGroupAlgebraCanonicalAugmentation R G)

/--
An all-finite completed group-algebra element lies in the canonical augmentation ideal iff the
canonical augmentation sends it to zero.
-/
@[simp]
theorem mem_completedGroupAlgebraCanonicalAugmentationIdeal_iff
    {R : Type u} {G : Type v} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {x : CompletedGroupAlgebraCarrier R G} :
    x ∈ completedGroupAlgebraCanonicalAugmentationIdeal R G ↔
      completedGroupAlgebraCanonicalAugmentation R G x = 0 :=
  Iff.rfl

/-- The inclusion of the canonical completed augmentation ideal is injective. -/
theorem completedGroupAlgebraCanonicalAugmentationIdeal_subtype_injective :
    Function.Injective
      (fun x : completedGroupAlgebraCanonicalAugmentationIdeal R G =>
        (x : CompletedGroupAlgebraCarrier R G)) := by
  intro x y hxy
  exact Subtype.ext hxy

/--
The canonical completed augmentation ideal is exactly the kernel of the canonical augmentation.
-/
theorem exact_completedGroupAlgebraCanonicalAugmentationIdeal_subtype :
    Function.Exact
      (fun x : completedGroupAlgebraCanonicalAugmentationIdeal R G =>
        (x : CompletedGroupAlgebraCarrier R G))
      (completedGroupAlgebraCanonicalAugmentation R G) := by
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
theorem completedGroupAlgebraCanonicalAugmentation_shortExact :
    Function.Injective
        (fun x : completedGroupAlgebraCanonicalAugmentationIdeal R G =>
          (x : CompletedGroupAlgebraCarrier R G)) ∧
      Function.Exact
        (fun x : completedGroupAlgebraCanonicalAugmentationIdeal R G =>
          (x : CompletedGroupAlgebraCarrier R G))
        (completedGroupAlgebraCanonicalAugmentation R G) ∧
      Function.Surjective (completedGroupAlgebraCanonicalAugmentation R G) := by
  exact ⟨completedGroupAlgebraCanonicalAugmentationIdeal_subtype_injective (R := R) (G := G),
    exact_completedGroupAlgebraCanonicalAugmentationIdeal_subtype (R := R) (G := G),
    completedGroupAlgebraCanonicalAugmentation_surjective (R := R) (G := G)⟩

/--
The all-finite augmentation ideal pulls back along the from-in-class comparison map to the
class-indexed augmentation ideal.
-/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationIdeal_comap_fromInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    Ideal.comap (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG)
        (completedGroupAlgebraCanonicalAugmentationIdeal R G) =
      completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C := by
  ext x
  rw [Ideal.mem_comap, mem_completedGroupAlgebraCanonicalAugmentationIdeal_iff,
    mem_completedGroupAlgebraCanonicalAugmentationIdealInClass_iff,
    completedGroupAlgebraFromInClassRingHom_apply,
    completedGroupAlgebraCanonicalAugmentation_fromInClass]

/--
The from-in-class comparison map sends the class-indexed augmentation ideal into the all-finite
augmentation ideal.
-/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationIdealInClass_map_fromInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    Ideal.map (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG)
        (completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C ) =
      completedGroupAlgebraCanonicalAugmentationIdeal R G := by
  rw [← completedGroupAlgebraCanonicalAugmentationIdeal_comap_fromInClass
    (R := R) (G := G) C hForm hG]
  exact Ideal.map_comap_of_surjective
    (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG)
    (completedGroupAlgebraFromInClass_surjective (R := R) (G := G) C hForm hG)
    (completedGroupAlgebraCanonicalAugmentationIdeal R G)

/--
The all-finite-to-in-class comparison map preserves and reflects membership in the canonical
augmentation ideal.
-/
@[simp]
theorem completedGroupAlgebraToInClass_mem_canonicalAugmentationIdeal_iff
    {R : Type u} {G : Type v} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    {x : CompletedGroupAlgebraCarrier R G} :
    completedGroupAlgebraToInClassRingHom (R := R) (G := G) C x ∈
        completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C ↔
      x ∈ completedGroupAlgebraCanonicalAugmentationIdeal R G := by
  rw [mem_completedGroupAlgebraCanonicalAugmentationIdealInClass_iff,
    mem_completedGroupAlgebraCanonicalAugmentationIdeal_iff]
  have haug := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraCanonicalAugmentationInClass_comp_toInClass
        (R := R) (G := G) C ))
    x
  change completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C
      (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C x) =
    completedGroupAlgebraCanonicalAugmentation R G x at haug
  rw [haug]

/--
The class-indexed augmentation ideal pulls back along the to-in-class comparison map to the
all-finite augmentation ideal.
-/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationIdealInClass_comap_toInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Ideal.comap (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C )
        (completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C ) =
      completedGroupAlgebraCanonicalAugmentationIdeal R G := by
  ext x
  exact completedGroupAlgebraToInClass_mem_canonicalAugmentationIdeal_iff
    (R := R) (G := G) C

/--
The to-in-class comparison map sends the all-finite augmentation ideal into the class-indexed
augmentation ideal.
-/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationIdeal_map_toInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    Ideal.map (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C )
        (completedGroupAlgebraCanonicalAugmentationIdeal R G) =
      completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C := by
  rw [← completedGroupAlgebraCanonicalAugmentationIdealInClass_comap_toInClass
    (R := R) (G := G) C ]
  exact Ideal.map_comap_of_surjective
    (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C )
    (completedGroupAlgebraToInClass_surjective (R := R) (G := G) C hForm hG)
    (completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C )

/--
A functorial all-finite completed group-algebra map sends augmentation generators to their
images.
-/
@[simp]
theorem completedGroupAlgebraMap_sub_one_of
    (φ : G →* H) (hφ : Continuous φ) (g : G) :
    completedGroupAlgebraMap (G := G) (H := H) R φ hφ
        (completedGroupAlgebraOf R G g - 1) =
      completedGroupAlgebraOf R H (φ g) - 1 := by
  rw [map_sub, completedGroupAlgebraMap_of, map_one]

/--
A functorial all-finite completed group-algebra map preserves and reflects membership in the
canonical augmentation ideal.
-/
@[simp]
theorem completedGroupAlgebraMap_mem_canonicalAugmentationIdeal_iff
    {R : Type u} {G : Type v} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* H) (hφ : Continuous φ)
    {x : CompletedGroupAlgebraCarrier R G} :
    completedGroupAlgebraMap (G := G) (H := H) R φ hφ x ∈
        completedGroupAlgebraCanonicalAugmentationIdeal R H ↔
      x ∈ completedGroupAlgebraCanonicalAugmentationIdeal R G := by
  rw [mem_completedGroupAlgebraCanonicalAugmentationIdeal_iff,
    mem_completedGroupAlgebraCanonicalAugmentationIdeal_iff,
    completedGroupAlgebraCanonicalAugmentation_map]

/--
Pulling back the target canonical augmentation ideal along a completed group-algebra map gives
the source canonical augmentation ideal.
-/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationIdeal_comap_map
    (φ : G →* H) (hφ : Continuous φ) :
    Ideal.comap (completedGroupAlgebraMap (G := G) (H := H) R φ hφ)
        (completedGroupAlgebraCanonicalAugmentationIdeal R H) =
      completedGroupAlgebraCanonicalAugmentationIdeal R G := by
  ext x
  exact completedGroupAlgebraMap_mem_canonicalAugmentationIdeal_iff
    (R := R) (G := G) (H := H) φ hφ

/--
A surjective functorial map sends the canonical completed augmentation ideal onto the target
canonical augmentation ideal.
-/
theorem completedGroupAlgebraCanonicalAugmentationIdeal_map_functorial_of_surjective
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (φ : G →* H) (hφ : Continuous φ)
    (hφsurj : Function.Surjective φ) :
    Ideal.map (completedGroupAlgebraMap (G := G) (H := H) R φ hφ)
        (completedGroupAlgebraCanonicalAugmentationIdeal R G) =
      completedGroupAlgebraCanonicalAugmentationIdeal R H := by
  rw [← completedGroupAlgebraCanonicalAugmentationIdeal_comap_map
    (R := R) (G := G) (H := H) φ hφ]
  exact Ideal.map_comap_of_surjective
    (completedGroupAlgebraMap (G := G) (H := H) R φ hφ)
    (completedGroupAlgebraMap_surjective_of_surjective
      (R := R) (G := G) (H := H) φ hφ hφsurj)
    (completedGroupAlgebraCanonicalAugmentationIdeal R H)
end

end CompletedGroupAlgebra
