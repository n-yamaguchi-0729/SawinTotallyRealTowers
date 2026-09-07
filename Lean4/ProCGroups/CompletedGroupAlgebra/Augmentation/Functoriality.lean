import ProCGroups.CompletedGroupAlgebra.Augmentation.AugmentationIdeal

set_option autoImplicit false

/-!
# Functoriality of augmentation

Maps of in-class completed group algebras commute with canonical augmentation. This file derives
the corresponding comap and image formulas for augmentation ideals, including the surjective
case.
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

/-- The in-class canonical augmentation is natural under functorial completed maps. -/
@[simp 900]
theorem completedGroupAlgebraCanonicalAugmentationInClass_map
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (x : CompletedGroupAlgebraInClass C R G) :
    completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := H) C
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ x) =
      completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C x := by
  let V : CompletedGroupAlgebraIndexInClass H C :=
    terminalCompletedGroupAlgebraIndexInClass (G := H) C
  calc
    completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := H) C
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ x)
        =
      completedGroupAlgebraAugmentationAtInClass C R H  V
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ x) := by
          exact completedGroupAlgebraCanonicalAugmentationInClass_eq_at
            (R := R) (G := H) C V
            (completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ x)
    _ =
      completedGroupAlgebraStageAugmentationInClass C R H V
        (completedGroupAlgebraFunctorialStageMapInClass
          (G := G) (H := H) C hHer (R := R) φ hφ V
          (completedGroupAlgebraProjectionInClass C R G
            (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x)) := by
          rw [completedGroupAlgebraAugmentationAtInClass,
              completedGroupAlgebraProjectionInClass_map]
    _ =
      completedGroupAlgebraStageAugmentationInClass C R G
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)
        (completedGroupAlgebraProjectionInClass C R G
          (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x) := by
          have hstage := congrFun
            (congrArg DFunLike.coe
              (completedGroupAlgebraStageAugmentationInClass_comp_functorialStageMapInClass
                (R := R) (G := G) (H := H) C hHer φ hφ V))
            (completedGroupAlgebraProjectionInClass C R G
              (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x)
          exact hstage
    _ =
      completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C x := by
          exact (completedGroupAlgebraCanonicalAugmentationInClass_eq_at
            (R := R) (G := G) C
            (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) x).symm

/-- Composing an in-class completed map with augmentation gives the source augmentation. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationInClass_comp_map
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := H) C ).comp
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ) =
      completedGroupAlgebraCanonicalAugmentationInClass (R := R) (G := G) C := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraCanonicalAugmentationInClass_map
    (R := R) (G := G) (H := H) C hHer φ hφ x

/--
A functorial in-class completed group-algebra map preserves and reflects membership in the
canonical augmentation ideal.
-/
@[simp]
theorem completedGroupAlgebraMapInClass_mem_canonicalAugmentationIdeal_iff
    {R : Type u} {G : Type v} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {C : ProCGroups.FiniteGroupClass.{v}}
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ)
    {x : CompletedGroupAlgebraInClass C R G} :
    completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ x ∈
        completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := H) C ↔
      x ∈ completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C := by
  rw [mem_completedGroupAlgebraCanonicalAugmentationIdealInClass_iff,
    mem_completedGroupAlgebraCanonicalAugmentationIdealInClass_iff,
    completedGroupAlgebraCanonicalAugmentationInClass_map]

/-- The \(C\)-indexed canonical augmentation ideal is pulled back to itself by functorial maps. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentationIdealInClass_comap_map
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) :
    Ideal.comap (completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ)
        (completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := H) C ) =
      completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C := by
  ext x
  exact completedGroupAlgebraMapInClass_mem_canonicalAugmentationIdeal_iff
    (R := R) (G := G) (H := H) (C := C) hHer φ hφ

/--
A surjective functorial map sends the \(C\)-indexed canonical augmentation ideal onto the target
canonical augmentation ideal.
-/
theorem completedGACanonicalAugmentationIdealInClass_map_functorial_of_surj
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (hH : HasOpenNormalBasisInClass C H)
    (φ : G →* H) (hφ : Continuous φ) (hφsurj : Function.Surjective φ) :
    Ideal.map (completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ)
        (completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := G) C ) =
      completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := H) C := by
  rw [← completedGroupAlgebraCanonicalAugmentationIdealInClass_comap_map
    (R := R) (G := G) (H := H) C hHer φ hφ]
  exact Ideal.map_comap_of_surjective
    (completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ)
    (completedGroupAlgebraMapInClass_surjective_of_surjective
      (R := R) (G := G) (H := H) C hForm hHer hH φ hφ hφsurj)
    (completedGroupAlgebraCanonicalAugmentationIdealInClass (R := R) (G := H) C )

end

end CompletedGroupAlgebra
