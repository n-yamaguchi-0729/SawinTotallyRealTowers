import ProCGroups.ProP.Fox.ModPBoundary
import ProCGroups.FoxDifferential.Completed.FreeProC.RelationReflection
import ProCGroups.FoxDifferential.Completed.FiniteStage.RelationRealization

set_option autoImplicit false
/-!
# Finite mod-p Fox stages of a presentation

A finite `p`-group quotient of the presented group determines a reflected
finite Fox stage.  Relation-ideal differentiation supplies module-level and
function-level exactness of the relation boundary followed by the Fox
boundary at that stage.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open CrowellExactSequence
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

/-- The `p`-coefficient differential-module index over a chosen target
finite `p`-group quotient. -/
def presentationModPFiniteStageIndex
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    ZCCompletedDifferentialModuleIndex
      (FiniteGroupClass.pGroup p) P.quotient.toMonoidHom :=
  zcCompletedDifferentialModuleComapIndex
    (FiniteGroupClass.pGroup p)
    (FiniteGroupClass.pGroup_hereditary p)
    P.quotient
    (modPCoefficientIndex p, OrderDual.toDual ⟨U, hU⟩)

/-- The reflected free-group kernel at the selected mod-`p` stage. -/
abbrev presentationModPFiniteStageKernel
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    Subgroup (FreeGroup (ULift.{u} (Fin d))) :=
  freeProCRelationReflectionTargetStageKernel
    sourceData P.basisCard P.quotient
      (presentationModPFiniteStageIndex P U hU)

/-- The reflected target quotient at the selected mod-`p` stage. -/
abbrev presentationModPFiniteStageTarget
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) : Type u :=
  foxAlgebraicStageTargetQuotient
    (presentationModPFiniteStageKernel P U hU)

/-- The canonical comparison from `G/U` to the reflected free quotient. -/
def presentationModPFiniteStageQMap
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    (G ⧸ (U : Subgroup G)) →* presentationModPFiniteStageTarget P U hU :=
  freeProCRelationReflectionTargetStageQMap
    sourceData P.basisCard P.quotient P.quotient_surjective
      (presentationModPFiniteStageIndex P U hU)

/-- The quotient comparison is injective. -/
theorem presentationModPFiniteStageQMap_injective
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    Function.Injective (presentationModPFiniteStageQMap P U hU) := by
  let _ : DiscreteTopology
      (FoxDifferential.CompletedGroupAlgebraQuotientInClass G
        (FiniteGroupClass.pGroup p)
        (presentationModPFiniteStageIndex P U hU).target.2) :=
    QuotientGroup.discreteTopology
      (ProCGroups.openNormalSubgroup_isOpen (G := G)
        ((OrderDual.ofDual
          (presentationModPFiniteStageIndex P U hU).target.2).1 :
            OpenNormalSubgroup G))
  unfold presentationModPFiniteStageQMap
    freeProCRelationReflectionTargetStageQMap
  exact freeProCFiniteQuotientStageQMap_injective
    (C := FiniteGroupClass.pGroup p)
    (fun x : ULift.{u} (Fin d) ↦
      P.quotient (freeProCReflectionFamily
        (C := FiniteGroupClass.pGroup p) sourceData P.basisCard x))
    (presentationModPFiniteStageIndex P U hU).target.2
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := FiniteGroupClass.pGroup p)
      (fun x : ULift.{u} (Fin d) ↦
        P.quotient (freeProCReflectionFamily
          (C := FiniteGroupClass.pGroup p) sourceData P.basisCard x))
      (presentationModPFiniteStageIndex P U hU).target.2
      (freeProCReflectionFamily_target_generates
        (C := FiniteGroupClass.pGroup p) sourceData P.basisCard
        P.quotient P.quotient_surjective))

/-- The quotient comparison identifies each chosen presentation generator
with the corresponding generator of the reflected free quotient. -/
theorem presentationModPFiniteStageQMap_generator
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (x : ULift.{u} (Fin d)) :
    presentationModPFiniteStageQMap P U hU
        (QuotientGroup.mk (P.quotient (presentationChosenGenerator P x))) =
      QuotientGroup.mk'
        (presentationModPFiniteStageKernel P U hU) (FreeGroup.of x) := by
  exact freeProCRelationReflectionTargetStageQMap_generator
    sourceData P.basisCard P.quotient P.quotient_surjective
      (presentationModPFiniteStageIndex P U hU) x

/-- The selected relation-reflection stage has coefficient modulus `p`. -/
theorem presentationModPFiniteStageIndex_modulus
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    (presentationModPFiniteStageIndex P U hU).target.1.modulus = p :=
  rfl

/-- Relation-ideal differentiation gives module-level exactness at the
selected mod-`p` reflected stage. -/
theorem presentationModPFiniteStageRelationBoundaryModuleExact
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    foxAlgebraicStageRelationBoundaryModuleExact
      (X := ULift.{u} (Fin d))
      (presentationModPFiniteStageKernel P U hU) p := by
  exact freeProCRelationReflection_finiteStage_relationBoundaryModuleExact
    sourceData P.basisCard P.quotient
      (presentationModPFiniteStageIndex P U hU)

/-- The finite-stage relation boundary followed by the Fox boundary is exact. -/
theorem presentationModPFiniteStageRelationBoundaryExact
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    foxAlgebraicStageRelationBoundaryExact
      (X := ULift.{u} (Fin d))
      (presentationModPFiniteStageKernel P U hU) p := by
  exact foxAlgebraicStageRelationBoundaryExact_of_relationBoundaryModuleExact
    (X := ULift.{u} (Fin d))
    (presentationModPFiniteStageKernel P U hU) p
    (presentationModPFiniteStageRelationBoundaryModuleExact P U hU)

end

end ClassFieldTower.ProP
