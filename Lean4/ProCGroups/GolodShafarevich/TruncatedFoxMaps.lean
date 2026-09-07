import ProCGroups.ProP.Fox.ModPFilteredLifting
import ProCGroups.GolodShafarevich.GradedPieces
import Mathlib.LinearAlgebra.Quotient.Pi

set_option autoImplicit false
/-!
# Truncated mod-p Fox maps

This file descends the completed relation matrix, Fox boundary, and canonical
augmentation to the shifted closed-augmentation quotients used in the
truncated Golod--Shafarevich sequence.
-/

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

/-- The relation source after passing coordinatewise to shifted truncations. -/
abbrev PresentationModPTruncatedRelationSource (ν : Fin r → ℕ) (N : ℕ) :=
  ∀ j : Fin r,
    ShiftedAugmentationTruncation (p := p) (G := G) N (ν j)

/-- The Fox-coordinate module after truncation, with the boundary shift. -/
abbrev PresentationModPTruncatedFoxCoordinates (N : ℕ) :=
  Fin d → ShiftedAugmentationTruncation (p := p) (G := G) N 1

/-- Reindex the universe-lifted presentation coordinates by `Fin d`. -/
def presentationModPFoxCoordinateFinEquiv :
    (Fin d → ModPCompletedGroupAlgebra p G) ≃ₗ[ModPCompletedGroupAlgebra p G]
      PresentationModPFoxCoordinates (p := p) (d := d) (G := G) where
  toFun v i := v i.down
  invFun v i := v (ULift.up i)
  left_inv v := rfl
  right_inv v := by
    funext i
    cases i
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private abbrev relationTruncationFamily (ν : Fin r → ℕ) (N : ℕ)
    (j : Fin r) : Submodule (ZMod p) (ModPCompletedGroupAlgebra p G) :=
  shiftedClosedAugmentationSubmodule (p := p) (G := G) N (ν j)

private abbrev foxTruncationFamily (N : ℕ) (_i : Fin d) :
    Submodule (ZMod p) (ModPCompletedGroupAlgebra p G) :=
  shiftedClosedAugmentationSubmodule (p := p) (G := G) N 1

private abbrev relationPiFiltration (ν : Fin r → ℕ) (N : ℕ) :
    Submodule (ZMod p) (Fin r → ModPCompletedGroupAlgebra p G) :=
  Submodule.pi Set.univ (relationTruncationFamily (p := p) (G := G) ν N)

private abbrev foxPiFiltration (N : ℕ) :
    Submodule (ZMod p) (Fin d → ModPCompletedGroupAlgebra p G) :=
  Submodule.pi Set.univ (foxTruncationFamily (p := p) (G := G) (d := d) N)

private def presentationModPRelationMatrixFin
    (P : FiniteProPPresentation p d r sourceData G) :
    (Fin r → ModPCompletedGroupAlgebra p G) →ₗ[ZMod p]
      (Fin d → ModPCompletedGroupAlgebra p G) :=
  ((presentationModPFoxCoordinateFinEquiv (p := p) (d := d) (G := G)).symm.toLinearMap.comp
    (presentationModPRelationMatrix P)).restrictScalars (ZMod p)

private def presentationModPFoxBoundaryFin
    (P : FiniteProPPresentation p d r sourceData G) :
    (Fin d → ModPCompletedGroupAlgebra p G) →ₗ[ZMod p]
      ModPCompletedGroupAlgebra p G :=
  ((presentationModPFoxBoundary P).comp
    (presentationModPFoxCoordinateFinEquiv (p := p) (d := d) (G := G)).toLinearMap).restrictScalars
      (ZMod p)

private theorem relationMatrixFin_mem_foxPiFiltration
    (P : FiniteProPPresentation p d r sourceData G)
    (ν : Fin r → ℕ)
    (hν : ∀ j, P.RelatorZassenhausDepthAtLeast (ν j) j)
    (N : ℕ) :
    relationPiFiltration (p := p) (G := G) ν N ≤
      (foxPiFiltration (p := p) (G := G) (d := d) N).comap
        (presentationModPRelationMatrixFin P) := by
  intro a ha
  have ha' : a ∈ presentationModPWeightedRelationSourceFiltration
      (p := p) (G := G) ν N := by
    intro j
    exact ha j (Set.mem_univ j)
  have hmatrix :=
    presentationModPRelationMatrix_mem_coordinateFiltration P ν hν N ha'
  intro i _hi
  change (presentationModPRelationMatrix P a) (ULift.up i) ∈
    shiftedClosedAugmentationSubmodule (p := p) (G := G) N 1
  simpa [presentationModPRelationMatrixFin, foxTruncationFamily,
    shiftedClosedAugmentationSubmodule] using hmatrix (ULift.up i)

private theorem foxBoundaryFin_mem_truncation
    (P : FiniteProPPresentation p d r sourceData G)
    (N : ℕ) :
    foxPiFiltration (p := p) (G := G) (d := d) N ≤
      (shiftedClosedAugmentationSubmodule (p := p) (G := G) N 0).comap
        (presentationModPFoxBoundaryFin P) := by
  intro v hv
  have hv' :
      (presentationModPFoxCoordinateFinEquiv (p := p) (d := d) (G := G)) v ∈
        presentationModPFoxCoordinateFiltration
          (p := p) (d := d) (G := G) N := by
    intro i
    have hi := hv i.down (Set.mem_univ i.down)
    change v i.down ∈ closedAugmentationPower p G N
    simpa [foxTruncationFamily, shiftedClosedAugmentationSubmodule] using hi
  have hboundary :=
    presentationModPFoxBoundary_mem_closedAugmentationPower_succ P N hv'
  change presentationModPFoxBoundary P
      ((presentationModPFoxCoordinateFinEquiv
        (p := p) (d := d) (G := G)) v) ∈
    shiftedClosedAugmentationSubmodule (p := p) (G := G) N 0
  simpa [presentationModPFoxBoundaryFin,
    shiftedClosedAugmentationSubmodule] using hboundary

/-- The relation matrix induced on the shifted truncation quotients. -/
def presentationModPTruncatedRelationMap
    (P : FiniteProPPresentation p d r sourceData G)
    (ν : Fin r → ℕ)
    (hν : ∀ j, P.RelatorZassenhausDepthAtLeast (ν j) j)
    (N : ℕ) :
    PresentationModPTruncatedRelationSource (p := p) (G := G) ν N →ₗ[ZMod p]
      PresentationModPTruncatedFoxCoordinates (p := p) (d := d) (G := G) N :=
  (Submodule.quotientPi
      (foxTruncationFamily (p := p) (G := G) (d := d) N)).toLinearMap.comp
    (((relationPiFiltration (p := p) (G := G) ν N).mapQ
      (foxPiFiltration (p := p) (G := G) (d := d) N)
      (presentationModPRelationMatrixFin P)
      (relationMatrixFin_mem_foxPiFiltration P ν hν N)).comp
    (Submodule.quotientPi
      (relationTruncationFamily (p := p) (G := G) ν N)).symm.toLinearMap)

/-- The Fox boundary induced on the shifted truncation quotients. -/
def presentationModPTruncatedFoxBoundary
    (P : FiniteProPPresentation p d r sourceData G) (N : ℕ) :
    PresentationModPTruncatedFoxCoordinates (p := p) (d := d) (G := G) N →ₗ[ZMod p]
      ShiftedAugmentationTruncation (p := p) (G := G) N 0 :=
  ((foxPiFiltration (p := p) (G := G) (d := d) N).mapQ
      (shiftedClosedAugmentationSubmodule (p := p) (G := G) N 0)
      (presentationModPFoxBoundaryFin P)
      (foxBoundaryFin_mem_truncation P N)).comp
    (Submodule.quotientPi
      (foxTruncationFamily (p := p) (G := G) (d := d) N)).symm.toLinearMap

@[simp] theorem presentationModPTruncatedRelationMap_mk
    (P : FiniteProPPresentation p d r sourceData G)
    (ν : Fin r → ℕ)
    (hν : ∀ j, P.RelatorZassenhausDepthAtLeast (ν j) j)
    (N : ℕ) (a : Fin r → ModPCompletedGroupAlgebra p G) :
    presentationModPTruncatedRelationMap P ν hν N
        (fun j ↦ Submodule.Quotient.mk (a j)) =
      fun i ↦ Submodule.Quotient.mk
        ((presentationModPRelationMatrix P a) (ULift.up i)) := by
  let ps := relationTruncationFamily (p := p) (G := G) ν N
  have hs :
      (Submodule.quotientPi ps).symm.toLinearMap
          (fun j ↦ Submodule.Quotient.mk (a j)) =
        Submodule.Quotient.mk a := by
    change (Submodule.quotientPi ps).symm
        (fun j ↦ Submodule.Quotient.mk (a j)) = _
    rw [show (fun j ↦ Submodule.Quotient.mk (a j)) =
        (Submodule.quotientPi ps) (Submodule.Quotient.mk a) by rfl]
    exact (Submodule.quotientPi ps).symm_apply_apply _
  rw [presentationModPTruncatedRelationMap]
  simp only [LinearMap.comp_apply]
  rw [hs]
  rfl

@[simp] theorem presentationModPTruncatedFoxBoundary_mk
    (P : FiniteProPPresentation p d r sourceData G)
    (N : ℕ) (v : Fin d → ModPCompletedGroupAlgebra p G) :
    presentationModPTruncatedFoxBoundary P N
        (fun i ↦ Submodule.Quotient.mk (v i)) =
      Submodule.Quotient.mk
        (presentationModPFoxBoundary P
          ((presentationModPFoxCoordinateFinEquiv
            (p := p) (d := d) (G := G)) v)) := by
  let pt := foxTruncationFamily (p := p) (G := G) (d := d) N
  have ht :
      (Submodule.quotientPi pt).symm.toLinearMap
          (fun i ↦ Submodule.Quotient.mk (v i)) =
        Submodule.Quotient.mk v := by
    change (Submodule.quotientPi pt).symm
        (fun i ↦ Submodule.Quotient.mk (v i)) = _
    rw [show (fun i ↦ Submodule.Quotient.mk (v i)) =
        (Submodule.quotientPi pt) (Submodule.Quotient.mk v) by rfl]
    exact (Submodule.quotientPi pt).symm_apply_apply _
  rw [presentationModPTruncatedFoxBoundary]
  simp only [LinearMap.comp_apply]
  rw [ht]
  rfl

private def presentationModPAugmentationLinearMap :
    ModPCompletedGroupAlgebra p G →ₗ[ZMod p] ZMod p where
  toFun := completedGroupAlgebraCanonicalAugmentationInClass
    (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  map_add' x y := by simp
  map_smul' c x := by
    change completedGroupAlgebraCanonicalAugmentationInClass
        (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p) (c • x) =
      c • completedGroupAlgebraCanonicalAugmentationInClass
        (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p) x
    simp [Algebra.smul_def]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
private theorem shiftedTruncation_le_augmentation_ker (N : ℕ) :
    shiftedClosedAugmentationSubmodule (p := p) (G := G) N 0 ≤
      (presentationModPAugmentationLinearMap (p := p) (G := G)).ker := by
  intro x hx
  rw [LinearMap.mem_ker]
  have hxPower : x ∈ closedAugmentationPower p G (N + 1) := by
    simpa [shiftedClosedAugmentationSubmodule] using hx
  have hxOne : x ∈ closedAugmentationPower p G 1 :=
    closedAugmentationPower_antitone (p := p) (G := G) (by omega) hxPower
  have hclosed : IsClosed
      ((modPAugmentationIdeal p G : Ideal (ModPCompletedGroupAlgebra p G)) :
        Set (ModPCompletedGroupAlgebra p G)) := by
    change IsClosed
      ((completedGroupAlgebraCanonicalAugmentationInClass
        (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)) ⁻¹' {0})
    exact isClosed_singleton.preimage
      (continuous_completedGroupAlgebraCanonicalAugmentationInClass
        (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p))
  have hxIdeal : x ∈
      ((modPAugmentationIdeal p G : Ideal (ModPCompletedGroupAlgebra p G)) :
        Set (ModPCompletedGroupAlgebra p G)) := by
    change x ∈ closure
      (((modPAugmentationIdeal p G) ^ 1 :
        Ideal (ModPCompletedGroupAlgebra p G)) :
          Set (ModPCompletedGroupAlgebra p G)) at hxOne
    simpa only [Submodule.pow_one, hclosed.closure_eq] using hxOne
  change completedGroupAlgebraCanonicalAugmentationInClass
    (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p) x = 0
  exact hxIdeal

/-- The canonical augmentation induced on the unshifted truncation. -/
def presentationModPTruncatedAugmentation (N : ℕ) :
    ShiftedAugmentationTruncation (p := p) (G := G) N 0 →ₗ[ZMod p] ZMod p :=
  (shiftedClosedAugmentationSubmodule (p := p) (G := G) N 0).liftQ
    (presentationModPAugmentationLinearMap (p := p) (G := G))
    (shiftedTruncation_le_augmentation_ker (p := p) (G := G) N)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp] theorem presentationModPTruncatedAugmentation_mk
    (N : ℕ) (x : ModPCompletedGroupAlgebra p G) :
    presentationModPTruncatedAugmentation (p := p) (G := G) N
        (Submodule.Quotient.mk x) =
      completedGroupAlgebraCanonicalAugmentationInClass
        (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p) x :=
  rfl

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem presentationModPTruncatedRelationSource_mk_surjective
    (ν : Fin r → ℕ) (N : ℕ) :
    Function.Surjective
      (fun a : Fin r → ModPCompletedGroupAlgebra p G ↦
        (fun j ↦ Submodule.Quotient.mk (a j) :
          PresentationModPTruncatedRelationSource (p := p) (G := G) ν N)) := by
  classical
  intro x
  choose a ha using fun j ↦
    (shiftedClosedAugmentationSubmodule
      (p := p) (G := G) N (ν j)).mkQ_surjective (x j)
  refine ⟨a, ?_⟩
  funext j
  exact ha j

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem presentationModPTruncatedFoxCoordinates_mk_surjective (N : ℕ) :
    Function.Surjective
      (fun v : Fin d → ModPCompletedGroupAlgebra p G ↦
        (fun i ↦ Submodule.Quotient.mk (v i) :
          PresentationModPTruncatedFoxCoordinates
            (p := p) (d := d) (G := G) N)) := by
  classical
  intro x
  choose v hv using fun i ↦
    (shiftedClosedAugmentationSubmodule
      (p := p) (G := G) N 1).mkQ_surjective (x i)
  refine ⟨v, ?_⟩
  funext i
  exact hv i

/-- The induced relation map is killed by the induced Fox boundary. -/
theorem presentationModPTruncatedFoxBoundary_comp_relationMap
    (P : FiniteProPPresentation p d r sourceData G)
    (ν : Fin r → ℕ)
    (hν : ∀ j, P.RelatorZassenhausDepthAtLeast (ν j) j)
    (N : ℕ) :
    (presentationModPTruncatedFoxBoundary P N).comp
        (presentationModPTruncatedRelationMap P ν hν N) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ :=
    presentationModPTruncatedRelationSource_mk_surjective (p := p) (G := G) ν N x
  rw [LinearMap.comp_apply, presentationModPTruncatedRelationMap_mk,
    presentationModPTruncatedFoxBoundary_mk]
  have hreindex :
      presentationModPFoxCoordinateFinEquiv (p := p) (d := d) (G := G)
          (fun i ↦ (presentationModPRelationMatrix P a) (ULift.up i)) =
        presentationModPRelationMatrix P a := by
    ext i
    cases i
    rfl
  rw [hreindex]
  have hraw : presentationModPFoxBoundary P
      (presentationModPRelationMatrix P a) = 0 := by
    exact LinearMap.congr_fun
      (presentationModPFoxBoundary_comp_relationMatrix P) a
  rw [hraw]
  rfl

/-- The induced augmentation kills the induced Fox boundary. -/
theorem presentationModPTruncatedAugmentation_comp_foxBoundary
    (P : FiniteProPPresentation p d r sourceData G) (N : ℕ) :
    (presentationModPTruncatedAugmentation (p := p) (G := G) N).comp
        (presentationModPTruncatedFoxBoundary P N) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ :=
    presentationModPTruncatedFoxCoordinates_mk_surjective (p := p) (G := G) (d := d) N x
  rw [LinearMap.comp_apply, presentationModPTruncatedFoxBoundary_mk,
    presentationModPTruncatedAugmentation_mk]
  exact presentationModPFoxBoundary_mem_augmentationIdeal P
    (presentationModPFoxCoordinateFinEquiv
      (p := p) (d := d) (G := G) v)

end

end ClassFieldTower.ProP
