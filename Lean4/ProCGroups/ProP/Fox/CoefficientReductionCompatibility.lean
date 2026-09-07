import ProCGroups.ProP.Fox.CoefficientReduction
import ProCGroups.ProP.Zassenhaus.GroupLike

set_option autoImplicit false
/-!
# Compatibility of mod-p coefficient reduction

The continuous coefficient-reduction homomorphism preserves group-like
elements, commutes with augmentation, and carries the algebraic and closed
augmentation filtrations to their mod-`p` counterparts.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open FoxDifferential
open ProCGroups
open ProCGroups.Completion

noncomputable section

universe u

variable (p : ℕ) [Fact p.Prime]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Coefficient reduction carries an integral completed group-like element to
the corresponding mod-`p` completed group-like element. -/
@[simp]
theorem modPCoefficientReduction_groupLike (g : G) :
    modPCoefficientReduction p G
        (zcGroupLike (FiniteGroupClass.pGroup p) G g) =
      completedGroupAlgebraOfInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G g := by
  apply completedGroupAlgebraInClass_ext
    (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  intro U
  rw [completedGroupAlgebraProjectionInClass_modPCoefficientReduction]
  change zcCompletedGroupAlgebraProjection
      (FiniteGroupClass.pGroup p) G (modPCoefficientIndex p, U)
      (zcGroupLike (FiniteGroupClass.pGroup p) G g) =
    completedGroupAlgebraProjectionInClass
      (FiniteGroupClass.pGroup p) (ZMod p) G U
      (completedGroupAlgebraOfInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G g)
  rw [zcCompletedGroupAlgebraProjection_groupLike,
    completedGroupAlgebraProjectionInClass_of]
  simp only [ProCGroups.ProC.openNormalSubgroupInClassProj,
    QuotientGroup.mk'_apply]
  rfl

/-- Coefficient reduction carries `[g] - 1` to the mod-`p` group-like
difference. -/
@[simp]
theorem modPCoefficientReduction_groupLike_sub_one (g : G) :
    modPCoefficientReduction p G
        (zcGroupLike (FiniteGroupClass.pGroup p) G g - 1) =
      groupLikeDifference p G g := by
  simp only [map_sub, map_one, modPCoefficientReduction_groupLike,
    groupLikeDifference]

/-- Coefficient reduction commutes with augmentation after projecting the
pro-`p` integer coefficient to its distinguished mod-`p` coordinate. -/
theorem modPCoefficientReduction_augmentation
    (x : ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G) :
    completedGroupAlgebraCanonicalAugmentationInClass
        (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
        (modPCoefficientReduction p G x) =
      proCIntegerProj
        (C := (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}))
        (modPCoefficientIndex p)
        (zcCompletedGroupAlgebraAugmentation
          (FiniteGroupClass.pGroup p) G x) := by
  let U := terminalCompletedGroupAlgebraIndexInClass
    (G := G) (FiniteGroupClass.pGroup p)
  rw [completedGroupAlgebraCanonicalAugmentationInClass_eq_at
    (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p) U]
  change
    modNCompletedGroupAlgebraStageAugmentationInClass p G
        (FiniteGroupClass.pGroup p) U
        (zcCompletedGroupAlgebraProjection
          (FiniteGroupClass.pGroup p) G
          (modPCoefficientIndex p, U) x) = _
  exact
    (proCIntegerProj_zcCompletedGroupAlgebraAugmentation_eq_stage
      (FiniteGroupClass.pGroup p) G
      (modPCoefficientIndex p, U) x).symm

/-- Coefficient reduction sends the source augmentation ideal into the mod-`p`
augmentation ideal. -/
theorem modPCoefficientReduction_mem_augmentationIdeal
    {x : ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G}
    (hx : x ∈ zcCompletedGroupAlgebraAugmentationIdeal
      (FiniteGroupClass.pGroup p) G) :
    modPCoefficientReduction p G x ∈ modPAugmentationIdeal p G := by
  rw [mem_completedGroupAlgebraCanonicalAugmentationIdealInClass_iff,
    modPCoefficientReduction_augmentation]
  rw [mem_zcCompletedGroupAlgebraAugmentationIdeal_iff] at hx
  rw [hx]
  exact proCIntegerProj_zero (C := FiniteGroupClass.pGroup p)
    (modPCoefficientIndex p)

/-- Coefficient reduction sends each algebraic source augmentation-ideal power
into the corresponding mod-`p` ideal power. -/
theorem modPCoefficientReduction_mem_augmentationIdeal_pow
    (n : ℕ)
    {x : ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G}
    (hx : x ∈
      (zcCompletedGroupAlgebraAugmentationIdeal
        (FiniteGroupClass.pGroup p) G) ^ n) :
    modPCoefficientReduction p G x ∈ (modPAugmentationIdeal p G) ^ n :=
  ringHom_mem_ideal_pow
    (modPCoefficientReduction p G)
    (fun _ hy => modPCoefficientReduction_mem_augmentationIdeal p G hy)
    n hx

/-- The closure of the `n`-th source augmentation-ideal power. -/
def zcClosedAugmentationPower (n : ℕ) :
    Ideal (ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G) :=
  ((zcCompletedGroupAlgebraAugmentationIdeal
    (FiniteGroupClass.pGroup p) G) ^ n).closure

/-- Continuous coefficient reduction sends closed source augmentation powers
into the corresponding closed mod-`p` augmentation powers. -/
theorem modPCoefficientReduction_mem_closedAugmentationPower
    (n : ℕ)
    {x : ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G}
    (hx : x ∈ zcClosedAugmentationPower p G n) :
    modPCoefficientReduction p G x ∈ closedAugmentationPower p G n := by
  let sourcePower :
      Ideal (ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G) :=
    (zcCompletedGroupAlgebraAugmentationIdeal
      (FiniteGroupClass.pGroup p) G) ^ n
  let targetPower : Ideal (ModPCompletedGroupAlgebra p G) :=
    (modPAugmentationIdeal p G) ^ n
  change x ∈ sourcePower.closure at hx
  change modPCoefficientReduction p G x ∈ targetPower.closure
  apply map_mem_closure
    (f := modPCoefficientReduction p G)
    (s := (sourcePower : Set _))
    (t := (targetPower : Set _))
    (continuous_modPCoefficientReduction p G) hx
  intro y hy
  exact modPCoefficientReduction_mem_augmentationIdeal_pow p G n hy

end

end ClassFieldTower.ProP
