import ProCGroups.ProP.Fox.CompletedFiltration
import ProCGroups.ProP.Fox.ModPDensityExactness
import ProCGroups.ProP.Fox.ModPTailExactness

set_option autoImplicit false
/-!
# Filtered packaging for the mod-p Fox complex

The coordinate module is filtered coordinatewise by closed augmentation
powers.  A displayed relator of Zassenhaus depth at least `ν j` gives a row
of depth at least `ν j - 1`; this makes the relation matrix filtered when its
source is given the corresponding shifted filtration.  The Fox boundary
raises coordinate depth by one.

The final theorem packages these filtration bounds with the underlying
unfiltered exactness and the identification of the boundary range.  It does
not assert strictness of either filtered map.
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

/-- The coordinatewise closed-augmentation filtration on mod-`p` Fox vectors. -/
def presentationModPFoxCoordinateFiltration (n : ℕ) :
    Submodule (ModPCompletedGroupAlgebra p G)
      (PresentationModPFoxCoordinates (p := p) (d := d) (G := G)) where
  carrier := {v | ∀ i, v i ∈ closedAugmentationPower p G n}
  zero_mem' i := (closedAugmentationPower p G n).zero_mem
  add_mem' {v w} hv hw i :=
    (closedAugmentationPower p G n).add_mem (hv i) (hw i)
  smul_mem' a v hv i := by
    change a * v i ∈ closedAugmentationPower p G n
    exact (closedAugmentationPower p G n).mul_mem_left a (hv i)

/-- Membership in the coordinate filtration is coordinatewise membership. -/
@[simp]
theorem mem_presentationModPFoxCoordinateFiltration_iff
    (n : ℕ)
    (v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G)) :
    v ∈ presentationModPFoxCoordinateFiltration (p := p) (d := d) (G := G) n ↔
      ∀ i, v i ∈ closedAugmentationPower p G n :=
  Iff.rfl

/-- The source filtration shifted by the prescribed Zassenhaus depth `ν` of
each displayed relator. -/
def presentationModPWeightedRelationSourceFiltration
    (ν : Fin r → ℕ) (N : ℕ) :
    Submodule (ModPCompletedGroupAlgebra p G)
      (Fin r → ModPCompletedGroupAlgebra p G) where
  carrier := {a | ∀ j, a j ∈ closedAugmentationPower p G (N + 1 - ν j)}
  zero_mem' j := (closedAugmentationPower p G (N + 1 - ν j)).zero_mem
  add_mem' {a b} ha hb j :=
    (closedAugmentationPower p G (N + 1 - ν j)).add_mem (ha j) (hb j)
  smul_mem' c a ha j := by
    change c * a j ∈ closedAugmentationPower p G (N + 1 - ν j)
    exact (closedAugmentationPower p G (N + 1 - ν j)).mul_mem_left c (ha j)

/-- Membership in the weighted source filtration is the stated shifted
coordinatewise condition. -/
@[simp]
theorem mem_presentationModPWeightedRelationSourceFiltration_iff
    (ν : Fin r → ℕ) (N : ℕ)
    (a : Fin r → ModPCompletedGroupAlgebra p G) :
    a ∈ presentationModPWeightedRelationSourceFiltration
        (p := p) (G := G) ν N ↔
      ∀ j, a j ∈ closedAugmentationPower p G (N + 1 - ν j) :=
  Iff.rfl

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The mod-`p` Fox boundary sends coordinate depth `n` to augmentation
depth `n + 1`. -/
theorem presentationModPFoxBoundary_mem_closedAugmentationPower_succ
    (P : FiniteProPPresentation p d r sourceData G) (n : ℕ)
    {v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G)}
    (hv : v ∈ presentationModPFoxCoordinateFiltration
      (p := p) (d := d) (G := G) n) :
    presentationModPFoxBoundary P v ∈ closedAugmentationPower p G (n + 1) := by
  rw [presentationModPFoxBoundary_apply]
  apply Ideal.sum_mem
  intro i _
  apply closedAugmentationPower_mul_mem (p := p) (G := G) (hv i)
  rw [closedAugmentationPower, Submodule.pow_one]
  exact subset_closure
    (groupLikeDifference_mem_augmentationIdeal p G
      (P.quotient (presentationChosenGenerator P i)))

/-- With the source shifted by the displayed-relator depths, the relation
matrix preserves every target filtration depth. -/
theorem presentationModPRelationMatrix_mem_coordinateFiltration
    (P : FiniteProPPresentation p d r sourceData G)
    (ν : Fin r → ℕ)
    (hν : ∀ j, P.RelatorZassenhausDepthAtLeast (ν j) j)
    (N : ℕ) {a : Fin r → ModPCompletedGroupAlgebra p G}
    (ha : a ∈ presentationModPWeightedRelationSourceFiltration
      (p := p) (G := G) ν N) :
    presentationModPRelationMatrix P a ∈
      presentationModPFoxCoordinateFiltration
        (p := p) (d := d) (G := G) N := by
  intro i
  rw [presentationModPRelationMatrix, finiteFamilyLinearMap_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Ideal.sum_mem
  intro j _
  have hrow :
      displayedRelatorModPFoxRow P j i ∈
        closedAugmentationPower p G (ν j - 1) := by
    cases hdepth : ν j with
    | zero =>
        rw [Nat.zero_sub, closedAugmentationPower,
          Submodule.pow_zero, Ideal.one_eq_top]
        exact subset_closure (Set.mem_univ _)
    | succ n =>
        rw [Nat.succ_sub_one]
        exact displayedRelatorModPFoxDerivative_mem_closedAugmentationPower
          P n j i (by simpa only [hdepth] using hν j)
  have hproduct :
      a j * displayedRelatorModPFoxRow P j i ∈
        closedAugmentationPower p G ((N + 1 - ν j) + (ν j - 1)) :=
    closedAugmentationPower_mul_mem (p := p) (G := G) (ha j) hrow
  exact closedAugmentationPower_antitone (p := p) (G := G)
    (by omega) hproduct

/-- The filtered bounds together with the underlying exactness and the
augmentation-ideal description of the boundary range.  This package makes no
strict filtered-lifting claim. -/
theorem presentationModP_filteredRelationBoundary_package
    (P : FiniteProPPresentation p d r sourceData G)
    (ν : Fin r → ℕ)
    (hν : ∀ j, P.RelatorZassenhausDepthAtLeast (ν j) j) :
    Function.Exact (presentationModPRelationMatrix P)
        (presentationModPFoxBoundary P) ∧
      LinearMap.range (presentationModPFoxBoundary P) =
        (modPAugmentationIdeal p G :
          Submodule (ModPCompletedGroupAlgebra p G)
            (ModPCompletedGroupAlgebra p G)) ∧
      (∀ (n : ℕ)
          {v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G)},
        v ∈ presentationModPFoxCoordinateFiltration
            (p := p) (d := d) (G := G) n →
          presentationModPFoxBoundary P v ∈
            closedAugmentationPower p G (n + 1)) ∧
      ∀ (N : ℕ) {a : Fin r → ModPCompletedGroupAlgebra p G},
        a ∈ presentationModPWeightedRelationSourceFiltration
            (p := p) (G := G) ν N →
          presentationModPRelationMatrix P a ∈
            presentationModPFoxCoordinateFiltration
              (p := p) (d := d) (G := G) N := by
  exact ⟨presentationModPRelationMatrix_boundary_exact P,
    presentationModPFoxBoundary_range_eq_augmentationIdeal P,
    fun n _ hv ↦
      presentationModPFoxBoundary_mem_closedAugmentationPower_succ P n hv,
    fun N _ ha ↦
      presentationModPRelationMatrix_mem_coordinateFiltration P ν hν N ha⟩

end

end ClassFieldTower.ProP
