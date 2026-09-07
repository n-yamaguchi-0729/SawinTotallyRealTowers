import ProCGroups.ProP.Fox.CompletedOperatorCompatibility
import ProCGroups.ProP.Fox.FiltrationDrop
import ProCGroups.ProP.Presentation.RelatorDepth

set_option autoImplicit false
/-!
# Filtration drop for the completed presentation Fox operator

Each coordinate of the completed mod-`p` Fox operator is a continuous linear
map.  Its right Fox--Leibniz rule lowers the closed augmentation filtration by
one, so the Fox derivative of a group element of Zassenhaus depth at least
`n + 1` has every coordinate in target depth at least `n`.
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

/-- Evaluation of one coordinate of the completed presentation Fox operator,
bundled as a continuous linear map. -/
def presentationCompletedModPFoxCoordinate
    (P : FiniteProPPresentation p d r sourceData G)
    (i : ULift.{u} (Fin d)) :
    ModPCompletedGroupAlgebra p sourceData.carrier →L[ZMod p]
      ModPCompletedGroupAlgebra p G where
  toFun x := presentationCompletedModPFoxOperator P x i
  map_add' x y := by
    exact congrFun (map_add (presentationCompletedModPFoxOperator P) x y) i
  map_smul' c x := by
    exact congrFun (map_smul (presentationCompletedModPFoxOperator P) c x) i
  cont := (continuous_apply i).comp
    (presentationCompletedModPFoxOperator P).continuous

/-- A coordinate of the completed operator satisfies the right
Fox--Leibniz rule. -/
theorem presentationCompletedModPFoxCoordinate_rightLeibniz
    (P : FiniteProPPresentation p d r sourceData G)
    (i : ULift.{u} (Fin d))
    (x y : ModPCompletedGroupAlgebra p sourceData.carrier) :
    presentationCompletedModPFoxCoordinate P i (x * y) =
      algebraMap (ZMod p) (ModPCompletedGroupAlgebra p G)
          (completedGroupAlgebraCanonicalAugmentationInClass
            (R := ZMod p) (G := sourceData.carrier)
            (FiniteGroupClass.pGroup p) y) *
        presentationCompletedModPFoxCoordinate P i x +
      modPCompletedGroupAlgebraMap p P.quotient x *
        presentationCompletedModPFoxCoordinate P i y := by
  have h := congrFun
    (presentationCompletedModPFoxOperator_rightLeibniz P x y) i
  change presentationCompletedModPFoxOperator P (x * y) i =
    algebraMap (ZMod p) (ModPCompletedGroupAlgebra p G)
        (completedGroupAlgebraCanonicalAugmentationInClass
          (R := ZMod p) (G := sourceData.carrier)
          (FiniteGroupClass.pGroup p) y) *
      presentationCompletedModPFoxOperator P x i +
    modPCompletedGroupAlgebraMap p P.quotient x *
      presentationCompletedModPFoxOperator P y i
  simpa only [Pi.add_apply, Pi.mul_apply, Pi.algebraMap_apply] using h

/-- The presentation-induced completed group-algebra map sends the source
augmentation kernel into the target augmentation ideal. -/
theorem presentationModPCompletedGroupAlgebraMap_mem_augmentationIdeal
    (P : FiniteProPPresentation p d r sourceData G)
    {x : ModPCompletedGroupAlgebra p sourceData.carrier}
    (hx : x ∈ RingHom.ker
      (completedGroupAlgebraCanonicalAugmentationInClass
        (R := ZMod p) (G := sourceData.carrier)
        (FiniteGroupClass.pGroup p))) :
    modPCompletedGroupAlgebraMap p P.quotient x ∈
      modPAugmentationIdeal p G := by
  unfold modPCompletedGroupAlgebraMap
  exact (completedGroupAlgebraMapInClass_mem_canonicalAugmentationIdeal_iff
    (R := ZMod p) (G := sourceData.carrier) (H := G)
    (C := FiniteGroupClass.pGroup p)
    (FiniteGroupClass.pGroup_hereditary p)
    P.quotient.toMonoidHom P.quotient.continuous).2 hx

/-- Each coordinate of the completed Fox operator lowers closed augmentation
powers by one. -/
theorem presentationCompletedModPFoxCoordinate_mem_closedAugmentationPower
    (P : FiniteProPPresentation p d r sourceData G)
    (i : ULift.{u} (Fin d)) (n : ℕ)
    {x : ModPCompletedGroupAlgebra p sourceData.carrier}
    (hx : x ∈ closedAugmentationPower p sourceData.carrier (n + 1)) :
    presentationCompletedModPFoxCoordinate P i x ∈
      closedAugmentationPower p G n := by
  let _ : (modPAugmentationIdeal p G).IsTwoSided :=
    modPAugmentationIdeal_isTwoSided p G
  exact mem_ideal_pow_closure_of_continuous_foxOperator
    (completedGroupAlgebraCanonicalAugmentationInClass
      (R := ZMod p) (G := sourceData.carrier)
      (FiniteGroupClass.pGroup p))
    (modPCompletedGroupAlgebraMap p P.quotient)
    (algebraMap (ZMod p) (ModPCompletedGroupAlgebra p G))
    (presentationCompletedModPFoxCoordinate P i).toLinearMap.toAddMonoidHom
    (modPAugmentationIdeal p G)
    (fun _ hy ↦
      presentationModPCompletedGroupAlgebraMap_mem_augmentationIdeal P hy)
    (presentationCompletedModPFoxCoordinate_rightLeibniz P i)
    (presentationCompletedModPFoxCoordinate P i).continuous n hx

/-- The completed presentation Fox operator vanishes at the unit. -/
@[simp]
theorem presentationCompletedModPFoxOperator_one
    (P : FiniteProPPresentation p d r sourceData G) :
    presentationCompletedModPFoxOperator P 1 = 0 := by
  rw [← completedGroupAlgebraOfInClass_one
    (R := ZMod p) (G := sourceData.carrier)
    (FiniteGroupClass.pGroup p)]
  rw [presentationCompletedModPFoxOperator_apply_groupLike,
    ScalarCrossedHom.map_one]

/-- On a group-like difference, the completed operator is the original
group-level mod-`p` Fox derivative. -/
@[simp]
theorem presentationCompletedModPFoxOperator_groupLikeDifference
    (P : FiniteProPPresentation p d r sourceData G)
    (f : sourceData.carrier) :
    presentationCompletedModPFoxOperator P
        (groupLikeDifference p sourceData.carrier f) =
      presentationModPFoxDerivative P f := by
  change presentationCompletedModPFoxOperator P
    (completedGroupAlgebraOfInClass
      (FiniteGroupClass.pGroup p) (ZMod p) sourceData.carrier f - 1) = _
  rw [map_sub, presentationCompletedModPFoxOperator_apply_groupLike,
    presentationCompletedModPFoxOperator_one]
  exact sub_zero _

/-- On a group-like difference, a completed coordinate is the corresponding
group-level mod-`p` Fox derivative coordinate. -/
@[simp]
theorem presentationCompletedModPFoxCoordinate_groupLikeDifference
    (P : FiniteProPPresentation p d r sourceData G)
    (f : sourceData.carrier) (i : ULift.{u} (Fin d)) :
    presentationCompletedModPFoxCoordinate P i
        (groupLikeDifference p sourceData.carrier f) =
      presentationModPFoxDerivative P f i := by
  change presentationCompletedModPFoxOperator P
      (groupLikeDifference p sourceData.carrier f) i = _
  exact congrFun
    (presentationCompletedModPFoxOperator_groupLikeDifference P f) i

/-- A group element of Zassenhaus depth at least `n + 1` has every mod-`p`
Fox derivative coordinate in the target closed augmentation power `n`. -/
theorem presentationModPFoxDerivative_mem_closedAugmentationPower
    (P : FiniteProPPresentation p d r sourceData G)
    (n : ℕ) (f : sourceData.carrier) (i : ULift.{u} (Fin d))
    (hf : ZassenhausDepthAtLeast p (n + 1) f) :
    presentationModPFoxDerivative P f i ∈
      closedAugmentationPower p G n := by
  rw [← presentationCompletedModPFoxCoordinate_groupLikeDifference P f i]
  apply presentationCompletedModPFoxCoordinate_mem_closedAugmentationPower P i n
  exact hf

/-- Every coordinate of a displayed relator of depth at least `n + 1` lies in
the target closed augmentation power `n`. -/
theorem displayedRelatorModPFoxDerivative_mem_closedAugmentationPower
    (P : FiniteProPPresentation p d r sourceData G)
    (n : ℕ) (j : Fin r) (i : ULift.{u} (Fin d))
    (hj : P.RelatorZassenhausDepthAtLeast (n + 1) j) :
    presentationModPFoxDerivative P (P.relator j) i ∈
      closedAugmentationPower p G n :=
  presentationModPFoxDerivative_mem_closedAugmentationPower
    P n (P.relator j) i hj

end

end ClassFieldTower.ProP
