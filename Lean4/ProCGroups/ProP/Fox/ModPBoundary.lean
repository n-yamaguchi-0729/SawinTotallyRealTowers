import ProCGroups.ProP.Fox.ModPGroupDerivative
import ProCGroups.ProP.Fox.Rows
import ProCGroups.FoxDifferential.Completed.Continuous.TopologicalGeneration

set_option autoImplicit false
/-!
# Mod-p Fox boundary and displayed relation matrix

The chosen presentation generators define the completed mod-`p` Fox boundary.
The mod-`p` presentation derivative satisfies its fundamental formula, so the
displayed relator rows give a finite linear map whose composite with the
boundary is zero.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open CrowellExactSequence
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

/-- The chosen finite free generator attached to a presentation coordinate. -/
abbrev presentationChosenGenerator
    (P : FiniteProPPresentation p d r sourceData G)
    (i : ULift.{u} (Fin d)) : sourceData.carrier :=
  freeProCChosenULiftFamilyOfBasisCard sourceData P.basisCard i

/-- The mod-`p` Fox boundary determined by the images of the chosen generators. -/
def presentationModPFoxBoundary
    (P : FiniteProPPresentation p d r sourceData G) :
    PresentationModPFoxCoordinates (p := p) (d := d) (G := G) →ₗ[
      ModPCompletedGroupAlgebra p G] ModPCompletedGroupAlgebra p G :=
  foxBoundaryMap fun i ↦
    groupLikeDifference p G (P.quotient (presentationChosenGenerator P i))

/-- Evaluation of the presentation boundary is its finite Fox sum. -/
theorem presentationModPFoxBoundary_apply
    (P : FiniteProPPresentation p d r sourceData G)
    (v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G)) :
    presentationModPFoxBoundary P v =
      ∑ i, v i *
        groupLikeDifference p G (P.quotient (presentationChosenGenerator P i)) :=
  rfl

/-- The integral presentation derivative has standard values on the chosen generators. -/
theorem presentationFoxDerivative_chosenGenerator
    (P : FiniteProPPresentation p d r sourceData G)
    (i : ULift.{u} (Fin d)) :
    presentationFoxDerivative P (presentationChosenGenerator P i) =
      Pi.single i (1 : PresentationFoxCoefficientRing (p := p) (G := G)) := by
  change
    freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
      (C := FiniteGroupClass.pGroup p)
      (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree
        (C := FiniteGroupClass.pGroup p) sourceData P.basisCard)
      (fun j : ULift.{u} (Fin d) ↦
        P.quotient (freeProCChosenULiftFamilyOfBasisCard sourceData P.basisCard j))
      (presentationFoxClosedTargetBasis P)
      (freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
        (C := FiniteGroupClass.pGroup p)
        (fun j : ULift.{u} (Fin d) ↦
          P.quotient (freeProCChosenULiftFamilyOfBasisCard sourceData P.basisCard j)))
      (freeProCChosenULiftFamilyOfBasisCard sourceData P.basisCard i) =
        Pi.single i (1 : PresentationFoxCoefficientRing (p := p) (G := G))
  exact freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_generator
    (C := FiniteGroupClass.pGroup p)
    (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree
      (C := FiniteGroupClass.pGroup p) sourceData P.basisCard)
    (fun j : ULift.{u} (Fin d) ↦
      P.quotient (freeProCChosenULiftFamilyOfBasisCard sourceData P.basisCard j))
    (presentationFoxClosedTargetBasis P)
    (freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
      (C := FiniteGroupClass.pGroup p)
      (fun j : ULift.{u} (Fin d) ↦
        P.quotient (freeProCChosenULiftFamilyOfBasisCard sourceData P.basisCard j)))
    i

/-- The integral completed Fox boundary of the presentation derivative. -/
theorem presentationFoxBoundary_derivative
    (P : FiniteProPPresentation p d r sourceData G)
    (f : sourceData.carrier) :
    freeProCZCCompletedFoxBoundary
        (FiniteGroupClass.pGroup p)
        (fun i : ULift.{u} (Fin d) ↦
          P.quotient (presentationChosenGenerator P i))
        (presentationFoxDerivative P f) =
      zcCompletedGroupAlgebraBoundary
        (FiniteGroupClass.pGroup p) P.quotient.toMonoidHom f := by
  exact freeProCZCBoundary_of_topologicalGeneration
    (FiniteGroupClass.pGroup p)
    (freeProCChosenULiftFamilyOfBasisCard_generates sourceData P.basisCard)
    P.quotient.toMonoidHom (presentationFoxDerivative P)
    (continuous_presentationFoxDerivative P) P.quotient.continuous
    (presentationFoxDerivative_chosenGenerator P) f

/-- The mod-`p` Fox fundamental formula for the presentation derivative. -/
theorem presentationModPFoxBoundary_derivative
    (P : FiniteProPPresentation p d r sourceData G)
    (f : sourceData.carrier) :
    presentationModPFoxBoundary P (presentationModPFoxDerivative P f) =
      groupLikeDifference p G (P.quotient f) := by
  calc
    presentationModPFoxBoundary P (presentationModPFoxDerivative P f) =
        modPCoefficientReduction p G
          (freeProCZCCompletedFoxBoundary
            (FiniteGroupClass.pGroup p)
            (fun i : ULift.{u} (Fin d) ↦
              P.quotient (presentationChosenGenerator P i))
            (presentationFoxDerivative P f)) := by
      rw [presentationModPFoxBoundary_apply,
        freeProCZCCompletedFoxBoundary_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [presentationModPFoxDerivative_apply, map_mul,
        modPCoefficientReduction_groupLike_sub_one]
    _ = modPCoefficientReduction p G
        (zcCompletedGroupAlgebraBoundary
          (FiniteGroupClass.pGroup p) P.quotient.toMonoidHom f) := by
      rw [presentationFoxBoundary_derivative]
    _ = groupLikeDifference p G (P.quotient f) := by
      exact modPCoefficientReduction_groupLike_sub_one p G (P.quotient f)

/-- The mod-`p` Fox row of one displayed relator. -/
def displayedRelatorModPFoxRow
    (P : FiniteProPPresentation p d r sourceData G) (i : Fin r) :
    PresentationModPFoxCoordinates (p := p) (d := d) (G := G) :=
  presentationModPFoxDerivative P (P.relator i)

/-- The finite displayed relation matrix over the mod-`p` completed group algebra. -/
def presentationModPRelationMatrix
    (P : FiniteProPPresentation p d r sourceData G) :
    (Fin r → ModPCompletedGroupAlgebra p G) →ₗ[
      ModPCompletedGroupAlgebra p G]
      PresentationModPFoxCoordinates (p := p) (d := d) (G := G) :=
  finiteFamilyLinearMap (displayedRelatorModPFoxRow P)

/-- Each displayed relation row is killed by the mod-`p` Fox boundary. -/
@[simp]
theorem presentationModPFoxBoundary_displayedRelatorModPFoxRow
    (P : FiniteProPPresentation p d r sourceData G) (i : Fin r) :
    presentationModPFoxBoundary P (displayedRelatorModPFoxRow P i) = 0 := by
  rw [displayedRelatorModPFoxRow, presentationModPFoxBoundary_derivative]
  rw [show P.quotient (P.relator i) = 1 from P.relator_mem_kernel i]
  exact groupLikeDifference_one p G

/-- The displayed relation matrix followed by the Fox boundary is zero. -/
theorem presentationModPFoxBoundary_comp_relationMatrix
    (P : FiniteProPPresentation p d r sourceData G) :
    (presentationModPFoxBoundary P).comp (presentationModPRelationMatrix P) = 0 := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, presentationModPRelationMatrix,
    finiteFamilyLinearMap_apply, map_sum]
  simp only [map_smul, presentationModPFoxBoundary_displayedRelatorModPFoxRow, smul_zero,
    Finset.sum_const_zero, LinearMap.zero_apply]

/-- The mod-`p` Fox boundary is continuous. -/
theorem continuous_presentationModPFoxBoundary
    (P : FiniteProPPresentation p d r sourceData G) :
    Continuous (presentationModPFoxBoundary P) :=
  continuous_foxBoundaryMap _

/-- The finite displayed relation matrix is continuous. -/
theorem continuous_presentationModPRelationMatrix
    (P : FiniteProPPresentation p d r sourceData G) :
    Continuous (presentationModPRelationMatrix P) := by
  change Continuous (fun a : Fin r → ModPCompletedGroupAlgebra p G ↦
    ∑ i, a i • displayedRelatorModPFoxRow P i)
  exact continuous_finsetSum _ fun i _ ↦ (continuous_apply i).smul continuous_const

/-- The relation-matrix range is the coefficient span of the displayed rows. -/
theorem presentationModPRelationMatrix_range_eq_span
    (P : FiniteProPPresentation p d r sourceData G) :
    LinearMap.range (presentationModPRelationMatrix P) =
      Submodule.span (ModPCompletedGroupAlgebra p G)
        (Set.range (displayedRelatorModPFoxRow P)) := by
  exact finiteFamilyLinearMap_range_eq_span (displayedRelatorModPFoxRow P)

/-- The range of the finite displayed relation matrix is compact. -/
theorem isCompact_range_presentationModPRelationMatrix
    (P : FiniteProPPresentation p d r sourceData G) :
    IsCompact (Set.range (presentationModPRelationMatrix P)) := by
  let _ : CompactSpace (ModPCompletedGroupAlgebra p G) :=
    completedGroupAlgebraInClass_compactSpace
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  simpa only [Set.image_univ] using
    (isCompact_univ.image (continuous_presentationModPRelationMatrix P))

/-- The range of the finite displayed relation matrix is closed. -/
theorem isClosed_range_presentationModPRelationMatrix
    (P : FiniteProPPresentation p d r sourceData G) :
    IsClosed (Set.range (presentationModPRelationMatrix P)) := by
  let _ : T2Space (ModPCompletedGroupAlgebra p G) :=
    completedGroupAlgebraInClass_t2Space
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  exact (isCompact_range_presentationModPRelationMatrix P).isClosed

end

end ClassFieldTower.ProP
