import ProCGroups.ProP.Fox.ModPFilteredExactness

set_option autoImplicit false
/-!
# Strict filtered lifting for the mod-p Fox boundary

The completed Fox boundary is strict for the closed augmentation filtration:
every element of filtration depth `n + 1` has a coordinate preimage of depth
`n`.  The proof first shows that the boundary image of the coordinate layer is
closed, using compactness of the completed group algebra.  The raw power of the
augmentation ideal lies in this image by algebraic multiplication and the
unfiltered boundary-range theorem, so taking closures gives the strict lift.

Combining this result with unfiltered relation--boundary exactness gives the
source-level lifting statement needed for exactness after passing to the
shifted filtration quotients.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open FoxDifferential
open ProCGroups

noncomputable section

universe u

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Every element of closed augmentation depth `n + 1` is the boundary of a
Fox coordinate vector of depth `n`. -/
theorem presentationModPFoxBoundary_coordinateFiltration_surjective
    (P : FiniteProPPresentation p d r sourceData G) (n : ℕ)
    {x : ModPCompletedGroupAlgebra p G}
    (hx : x ∈ closedAugmentationPower p G (n + 1)) :
    ∃ v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G),
      v ∈ presentationModPFoxCoordinateFiltration
          (p := p) (d := d) (G := G) n ∧
        presentationModPFoxBoundary P v = x := by
  let A := ModPCompletedGroupAlgebra p G
  let V := PresentationModPFoxCoordinates (p := p) (d := d) (G := G)
  let F := presentationModPFoxCoordinateFiltration
    (p := p) (d := d) (G := G) n
  let I := modPAugmentationIdeal p G
  let : CompactSpace A :=
    completedGroupAlgebraInClass_compactSpace
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  let : T2Space A :=
    completedGroupAlgebraInClass_t2Space
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  let : (closedAugmentationPower p G n).IsTwoSided :=
    closedAugmentationPower_isTwoSided p G n
  have hpowerClosed :
      IsClosed (((closedAugmentationPower p G n : Ideal A) : Set A)) := by
    exact Submodule.isClosed_topologicalClosure (I ^ n)
  have hFclosed : IsClosed ((F : Submodule A V) : Set V) := by
    rw [show ((F : Submodule A V) : Set V) =
        ⋂ i, (fun v : V ↦ v i) ⁻¹' (closedAugmentationPower p G n : Set A) by
      ext v
      constructor
      · intro hv
        simp only [Set.mem_iInter, Set.mem_preimage]
        exact hv
      · intro hv
        simp only [Set.mem_iInter, Set.mem_preimage] at hv
        exact hv]
    exact isClosed_iInter fun i ↦ hpowerClosed.preimage (continuous_apply i)
  have himageClosed :
      IsClosed (presentationModPFoxBoundary P '' ((F : Submodule A V) : Set V)) :=
    (hFclosed.isCompact.image (continuous_presentationModPFoxBoundary P)).isClosed
  have hraw : ((I ^ (n + 1) : Ideal A) : Set A) ⊆
      presentationModPFoxBoundary P '' ((F : Submodule A V) : Set V) := by
    intro y hy
    rw [Submodule.pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      have hbRange : b ∈ LinearMap.range (presentationModPFoxBoundary P) := by
        rw [presentationModPFoxBoundary_range_eq_augmentationIdeal P]
        exact hb
      rcases hbRange with ⟨v, hv⟩
      refine ⟨a • v, ?_, ?_⟩
      · intro i
        change a * v i ∈ closedAugmentationPower p G n
        exact (closedAugmentationPower p G n).mul_mem_right (v i)
          (subset_closure ha)
      · simp only [map_smul, hv, smul_eq_mul]
    · intro y z hy hz
      rcases hy with ⟨v, hvF, hv⟩
      rcases hz with ⟨w, hwF, hw⟩
      refine ⟨v + w, ?_, ?_⟩
      · intro i
        exact (closedAugmentationPower p G n).add_mem (hvF i) (hwF i)
      · rw [map_add, hv, hw]
  change x ∈ closure ((I ^ (n + 1) : Ideal A) : Set A) at hx
  have hxImage := closure_mono hraw hx
  rw [himageClosed.closure_eq] at hxImage
  rcases hxImage with ⟨v, hvF, hv⟩
  exact ⟨v, hvF, hv⟩

/-- If a coordinate vector has boundary of depth `n + 1`, it differs from a
relation-matrix image by a coordinate vector of depth `n`. -/
theorem presentationModPRelationMatrix_lift_mod_coordinateFiltration
    (P : FiniteProPPresentation p d r sourceData G) (n : ℕ)
    (v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G))
    (hv : presentationModPFoxBoundary P v ∈
      closedAugmentationPower p G (n + 1)) :
    ∃ a : Fin r → ModPCompletedGroupAlgebra p G,
      v - presentationModPRelationMatrix P a ∈
        presentationModPFoxCoordinateFiltration
          (p := p) (d := d) (G := G) n := by
  rcases presentationModPFoxBoundary_coordinateFiltration_surjective
      P n hv with ⟨w, hwF, hw⟩
  have hcycle : presentationModPFoxBoundary P (v - w) = 0 := by
    rw [map_sub, hw, sub_self]
  have hrange :=
    (presentationModPRelationMatrix_boundary_exact P (v - w)).mp hcycle
  rcases hrange with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have heq : v - presentationModPRelationMatrix P a = w := by
    rw [ha]
    abel
  rw [heq]
  exact hwF

/-- The completed mod-`p` Fox--Crowell complex is filtered right-exact: the
relation matrix and boundary respect their shifted filtrations, the
underlying middle complex is exact, and every filtered boundary cycle admits
a relation lift modulo the target filtration. -/
theorem presentationModP_filteredRightExact
    (P : FiniteProPPresentation p d r sourceData G)
    (ν : Fin r → ℕ)
    (hν : ∀ j, P.RelatorZassenhausDepthAtLeast (ν j) j) :
    (∀ (N : ℕ) {a : Fin r → ModPCompletedGroupAlgebra p G},
        a ∈ presentationModPWeightedRelationSourceFiltration
            (p := p) (G := G) ν N →
          presentationModPRelationMatrix P a ∈
            presentationModPFoxCoordinateFiltration
              (p := p) (d := d) (G := G) N) ∧
      (∀ (n : ℕ)
          {v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G)},
        v ∈ presentationModPFoxCoordinateFiltration
            (p := p) (d := d) (G := G) n →
          presentationModPFoxBoundary P v ∈
            closedAugmentationPower p G (n + 1)) ∧
      Function.Exact (presentationModPRelationMatrix P)
        (presentationModPFoxBoundary P) ∧
      (∀ (n : ℕ)
          (v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G)),
        presentationModPFoxBoundary P v ∈
            closedAugmentationPower p G (n + 1) →
          ∃ a : Fin r → ModPCompletedGroupAlgebra p G,
            v - presentationModPRelationMatrix P a ∈
              presentationModPFoxCoordinateFiltration
                (p := p) (d := d) (G := G) n) ∧
      LinearMap.range (presentationModPFoxBoundary P) =
        (modPAugmentationIdeal p G :
          Submodule (ModPCompletedGroupAlgebra p G)
            (ModPCompletedGroupAlgebra p G)) := by
  exact ⟨fun N _ ha ↦
      presentationModPRelationMatrix_mem_coordinateFiltration P ν hν N ha,
    fun n _ hv ↦
      presentationModPFoxBoundary_mem_closedAugmentationPower_succ P n hv,
    presentationModPRelationMatrix_boundary_exact P,
    fun n v hv ↦
      presentationModPRelationMatrix_lift_mod_coordinateFiltration P n v hv,
    presentationModPFoxBoundary_range_eq_augmentationIdeal P⟩

end

end ClassFieldTower.ProP
