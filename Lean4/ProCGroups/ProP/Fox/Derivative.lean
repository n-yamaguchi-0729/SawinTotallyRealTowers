import ProCGroups.ProP.Presentation.Basic
import ProCGroups.FoxDifferential.Completed.FreeProC.NaturalTopology

set_option autoImplicit false
/-!
# Completed Fox derivatives of finite pro-p presentations

This leaf specializes the existing continuous completed Fox differential to
the concrete quotient map carried by a finite pro-`p` presentation.  The
formation and closed-target hypotheses are derived from the presentation; they
are not additional assumptions.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups
open CrowellExactSequence
open FoxDifferential

noncomputable section

universe u

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Finite `p`-groups form the full formation required by completed Fox
calculus. -/
theorem pGroupFullFormation :
    FiniteGroupClass.FullFormation (FiniteGroupClass.pGroup p) where
  melnikovFormation :=
    { formation := FiniteGroupClass.pGroup_formation p
      normalSubgroupClosed := fun N _ hN =>
        FiniteGroupClass.pGroup_subgroupClosed p N hN
      extensionClosed := FiniteGroupClass.pGroup_extensionClosed p }
  subgroupClosed := FiniteGroupClass.pGroup_subgroupClosed p

/-- Surjectivity of the presentation quotient supplies the closed pro-`p`
target used by the completed Fox derivative. -/
theorem presentationFoxClosedTargetBasis
    (P : FiniteProPPresentation p d r sourceData G) :
    ProC.HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p)
      (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (C := FiniteGroupClass.pGroup p)
        (fun i : ULift.{u} (Fin d) =>
          P.quotient
            (freeProCChosenULiftFamilyOfBasisCard
              sourceData P.basisCard i)) : Subgroup
        (ZCCompletedFoxSemidirect
          (FiniteGroupClass.pGroup p) (ULift.{u} (Fin d)) G)) :=
  freeProCClosedGeneratedTarget_proC_of_surjective
    (C := FiniteGroupClass.pGroup p)
    (hC := pGroupFullFormation (p := p))
    sourceData P.basisCard P.quotient P.quotient_surjective

/-- Completed pro-`p` integral Fox coordinates for the chosen finite basis. -/
abbrev PresentationFoxCoordinates :=
  ZCFreeFoxCoordinates
    (FiniteGroupClass.pGroup p) (X := ULift.{u} (Fin d)) (H := G)

/-- The completed coefficient ring acting on presentation Fox rows. -/
abbrev PresentationFoxCoefficientRing :=
  ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G

/-- The existing completed Fox derivative attached to the presentation. -/
def presentationFoxDerivative
    (P : FiniteProPPresentation p d r sourceData G) :
    ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar
        (FiniteGroupClass.pGroup p) P.quotient.toMonoidHom)
      (PresentationFoxCoordinates (p := p) (d := d) (G := G)) :=
  freeProCCompletedFoxDerivativeVectorForPresentation
    (C := FiniteGroupClass.pGroup p)
    (H := G)
    (pGroupFullFormation (p := p)).melnikovFormation.formation
    sourceData P.basisCard P.quotient P.quotient_surjective
    (presentationFoxClosedTargetBasis P)

/-- The presentation Fox derivative is continuous. -/
theorem continuous_presentationFoxDerivative
    (P : FiniteProPPresentation p d r sourceData G) :
    Continuous (presentationFoxDerivative P) := by
  change Continuous
    (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
      (C := FiniteGroupClass.pGroup p)
      (H := G)
      sourceData P.basisCard P.quotient
      (presentationFoxClosedTargetBasis P))
  exact
    continuous_freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
      (C := FiniteGroupClass.pGroup p)
      (H := G)
      sourceData P.basisCard P.quotient
      (presentationFoxClosedTargetBasis P)

end

end ClassFieldTower.ProP
