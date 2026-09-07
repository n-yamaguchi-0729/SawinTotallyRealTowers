import ProCGroups.ProP.Fox.ModPBoundary
import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.CanonicalMaps

set_option autoImplicit false
/-!
# Tail exactness of the mod-p Fox boundary

The completed mod-`p` Fox boundary has closed range.  Density of the
algebraic group algebra, together with the presentation fundamental formula,
identifies that range with the canonical augmentation ideal.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open FoxDifferential
open ProCGroups
open ProCGroups.ProC

noncomputable section

universe u

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The range of the completed mod-p Fox boundary is closed. -/
theorem isClosed_range_presentationModPFoxBoundary
    (P : FiniteProPPresentation p d r sourceData G) :
    IsClosed (Set.range (presentationModPFoxBoundary P)) := by
  let _ : CompactSpace (ModPCompletedGroupAlgebra p G) :=
    completedGroupAlgebraInClass_compactSpace
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  let _ : T2Space (ModPCompletedGroupAlgebra p G) :=
    completedGroupAlgebraInClass_t2Space
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  simpa only [Set.image_univ] using
    (isCompact_univ.image (continuous_presentationModPFoxBoundary P)).isClosed

/-- The completed Fox boundary lands in the canonical augmentation ideal. -/
theorem presentationModPFoxBoundary_mem_augmentationIdeal
    (P : FiniteProPPresentation p d r sourceData G)
    (v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G)) :
    presentationModPFoxBoundary P v ∈ modPAugmentationIdeal p G := by
  rw [presentationModPFoxBoundary_apply]
  exact Ideal.sum_mem _ fun i _ =>
    (modPAugmentationIdeal p G).mul_mem_left (v i)
      (groupLikeDifference_mem_augmentationIdeal p G _)

/-- Every standard completed augmentation generator is in the boundary range. -/
theorem groupLikeDifference_mem_presentationModPFoxBoundary_range
    (P : FiniteProPPresentation p d r sourceData G) (g : G) :
    groupLikeDifference p G g ∈ LinearMap.range (presentationModPFoxBoundary P) := by
  rcases P.quotient_surjective g with ⟨f, rfl⟩
  exact ⟨presentationModPFoxDerivative P f,
    presentationModPFoxBoundary_derivative P f⟩

/-- The dense algebraic augmentation ideal maps into the completed boundary range. -/
theorem toCompletedGroupAlgebraInClass_mem_presentationModPFoxBoundary_range
    (P : FiniteProPPresentation p d r sourceData G)
    (a : MonoidAlgebra (ZMod p) G)
    (ha : a ∈ groupAlgebraAugmentationIdeal (ZMod p) G) :
    toCompletedGroupAlgebraInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G a ∈
      LinearMap.range (presentationModPFoxBoundary P) := by
  rw [← groupAlgebraAugmentationGeneratorIdeal_eq_augmentationIdeal] at ha
  change a ∈ Submodule.span (MonoidAlgebra (ZMod p) G)
    (Set.range (groupAlgebraAugmentationGenerator (ZMod p) G)) at ha
  refine Submodule.span_induction
    (p := fun z _ =>
      toCompletedGroupAlgebraInClass
          (FiniteGroupClass.pGroup p) (ZMod p) G z ∈
        LinearMap.range (presentationModPFoxBoundary P))
    ?_ ?_ ?_ ?_ ha
  · rintro z ⟨g, rfl⟩
    change
      toCompletedGroupAlgebraInClassRingHom
          (FiniteGroupClass.pGroup p) (ZMod p) G
          (MonoidAlgebra.of (ZMod p) G g - 1) ∈ _
    rw [map_sub, map_one]
    exact groupLikeDifference_mem_presentationModPFoxBoundary_range P g
  · change toCompletedGroupAlgebraInClassRingHom
      (FiniteGroupClass.pGroup p) (ZMod p) G 0 ∈ _
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    change toCompletedGroupAlgebraInClassRingHom
      (FiniteGroupClass.pGroup p) (ZMod p) G (x + y) ∈ _
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    change toCompletedGroupAlgebraInClassRingHom
      (FiniteGroupClass.pGroup p) (ZMod p) G (a * x) ∈ _
    rw [map_mul]
    exact Submodule.smul_mem _
      (toCompletedGroupAlgebraInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G a) hx

/-- The completed mod-p Fox boundary has range equal to the canonical augmentation ideal. -/
theorem presentationModPFoxBoundary_range_eq_augmentationIdeal
    (P : FiniteProPPresentation p d r sourceData G) :
    LinearMap.range (presentationModPFoxBoundary P) =
      (modPAugmentationIdeal p G :
        Submodule (ModPCompletedGroupAlgebra p G)
          (ModPCompletedGroupAlgebra p G)) := by
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    exact presentationModPFoxBoundary_mem_augmentationIdeal P v
  · intro x hx
    let C := FiniteGroupClass.pGroup p
    let A := ModPCompletedGroupAlgebra p G
    let denseMap : MonoidAlgebra (ZMod p) G →ₐ[ZMod p] A :=
      toCompletedGroupAlgebraInClassAlgHom C (ZMod p) G
    let aug : A →+* ZMod p :=
      completedGroupAlgebraCanonicalAugmentationInClass
        (R := ZMod p) (G := G) C
    let adjust : A → A := fun y => y - algebraMap (ZMod p) A (aug y)
    have hdense : DenseRange denseMap := by
      exact denseRange_toCompletedGroupAlgebraInClass
        (R := ZMod p) (G := G) C
        (FiniteGroupClass.pGroup_formation p) P.targetProP
    have hxclosure : x ∈ closure (Set.range denseMap) := by
      rw [hdense.closure_range]
      exact Set.mem_univ x
    have hadjust : Continuous adjust := by
      exact continuous_id.sub
        ((continuous_completedGroupAlgebraAlgebraMapInClass
          (R := ZMod p) (G := G) C).comp
          (continuous_completedGroupAlgebraCanonicalAugmentationInClass
            (R := ZMod p) (G := G) C))
    have hmap : ∀ y ∈ Set.range denseMap,
        adjust y ∈ LinearMap.range (presentationModPFoxBoundary P) := by
      rintro y ⟨a, rfl⟩
      have ha0 :
          a - algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G)
              (groupAlgebraAugmentation (ZMod p) G a) ∈
            groupAlgebraAugmentationIdeal (ZMod p) G := by
        rw [mem_groupAlgebraAugmentationIdeal_iff]
        simp
      have hrange :=
        toCompletedGroupAlgebraInClass_mem_presentationModPFoxBoundary_range P _ ha0
      change adjust (denseMap a) ∈ _
      have haugA : aug (denseMap a) = groupAlgebraAugmentation (ZMod p) G a := by
        change completedGroupAlgebraCanonicalAugmentationInClass
            (R := ZMod p) (G := G) C
            (toCompletedGroupAlgebraInClass C (ZMod p) G a) = _
        exact canonicalAugmentationInClass_toCompleted
          (R := ZMod p) (G := G) C a
      have hadjustA :
          adjust (denseMap a) =
            denseMap (a - algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G)
              (groupAlgebraAugmentation (ZMod p) G a)) := by
        change denseMap a - algebraMap (ZMod p) A (aug (denseMap a)) = _
        rw [haugA, map_sub]
        congr 1
        exact (denseMap.commutes
          (groupAlgebraAugmentation (ZMod p) G a)).symm
      rw [hadjustA]
      change toCompletedGroupAlgebraInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G
          (a - algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G)
            (groupAlgebraAugmentation (ZMod p) G a)) ∈ _
      exact hrange
    have himage := map_mem_closure
      (f := adjust) (s := Set.range denseMap)
      (t := Set.range (presentationModPFoxBoundary P))
      hadjust hxclosure hmap
    rw [(isClosed_range_presentationModPFoxBoundary P).closure_eq] at himage
    have hxaug : aug x = 0 := by
      exact hx
    simpa [adjust, hxaug] using himage

end

end ClassFieldTower.ProP
