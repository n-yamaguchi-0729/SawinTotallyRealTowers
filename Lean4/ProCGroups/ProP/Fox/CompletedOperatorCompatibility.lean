import ProCGroups.ProP.Fox.CompletedLeibniz
import ProCGroups.ProP.Fox.CompletedOperator
import ProCGroups.ProP.Zassenhaus.Functoriality
import ProCGroups.CompletedGroupAlgebra.AllFiniteAugmentation.InClassComparison
import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.InClassNaturality

set_option autoImplicit false
/-!
# Fox--Leibniz compatibility for the completed mod-p operator

The universal all-finite lift of the mod-`p` presentation derivative inherits
its crossed-product law from group-like elements.  The comparison equivalence
between all-finite and pro-`p`-indexed completed group algebras then transports
this law to the completed operator used by the Zassenhaus filtration.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open ProCGroups

noncomputable section

universe u

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The continuous canonical augmentation of the all-finite completed group
algebra over `ZMod p`. -/
def allFiniteModPAugmentation (P : ProfiniteGrp.{u}) :
    CompletedGroupAlgebraCarrier (ZMod p) P →A[ZMod p] ZMod p where
  toAlgHom :=
    { toRingHom := completedGroupAlgebraCanonicalAugmentation (ZMod p) P
      commutes' := by
        intro a
        let U := terminalCompletedGroupAlgebraIndex P
        change completedGroupAlgebraStageAugmentation (ZMod p) P U
            (completedGroupAlgebraProjection (ZMod p) P U
              (algebraMap (ZMod p)
                (CompletedGroupAlgebraCarrier (ZMod p) P) a)) = a
        change groupAlgebraAugmentation (ZMod p)
            (CompletedGroupAlgebraQuotient P U)
            (algebraMap (ZMod p)
              (CompletedGroupAlgebraStage (ZMod p) P U) a) = a
        exact groupAlgebraAugmentation_algebraMap
          (ZMod p) (CompletedGroupAlgebraQuotient P U) a }
  cont := continuous_completedGroupAlgebraCanonicalAugmentation (ZMod p) P

omit [Fact p.Prime] in
/-- The all-finite mod-`p` augmentation sends every completed group-like
element to one. -/
@[simp]
theorem allFiniteModPAugmentation_groupLike
    (P : ProfiniteGrp.{u}) (g : P) :
    allFiniteModPAugmentation (p := p) P
        (completedGroupAlgebraOf (ZMod p) P g) = 1 :=
  completedGroupAlgebraCanonicalAugmentation_of
    (R := ZMod p) (G := P) g

/-- The continuous algebra map from the all-finite source completion to the
pro-`p`-indexed target completion induced by the presentation quotient. -/
def presentationAllFiniteModPCoefficient
    (P : FiniteProPPresentation p d r sourceData G) :
    CompletedGroupAlgebraCarrier (ZMod p) sourceData.carrier.obj →A[ZMod p]
      ModPCompletedGroupAlgebra p G where
  toAlgHom :=
    (completedGroupAlgebraToInClassAlgHom
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)).comp
      (completedGroupAlgebraMapAlgHom
        (G := sourceData.carrier) (H := G) (ZMod p)
        P.quotient.toMonoidHom P.quotient.continuous)
  cont :=
    (continuous_completedGroupAlgebraToInClass
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)).comp
      (continuous_completedGroupAlgebraMap
        (G := sourceData.carrier) (H := G) (ZMod p)
        P.quotient.toMonoidHom P.quotient.continuous)

/-- The quotient-induced coefficient map has the expected value on completed
group-like elements. -/
@[simp]
theorem presentationAllFiniteModPCoefficient_groupLike
    (P : FiniteProPPresentation p d r sourceData G)
    (f : sourceData.carrier) :
    presentationAllFiniteModPCoefficient P
        (completedGroupAlgebraOf (ZMod p) sourceData.carrier.obj f) =
      completedGroupAlgebraOfInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G (P.quotient f) := by
  change completedGroupAlgebraToInClass
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
      (completedGroupAlgebraMap
        (G := sourceData.carrier) (H := G) (ZMod p)
        P.quotient.toMonoidHom P.quotient.continuous
        (completedGroupAlgebraOf (ZMod p) sourceData.carrier.obj f)) = _
  rw [completedGroupAlgebraMap_of]
  exact completedGroupAlgebraToInClass_of
    (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p) (P.quotient f)

/-- The quotient coefficient acts diagonally on a completed Fox row. -/
def presentationAllFiniteModPCoordinateCoefficient
    (P : FiniteProPPresentation p d r sourceData G) :
    CompletedGroupAlgebraCarrier (ZMod p) sourceData.carrier.obj →A[ZMod p]
      PresentationModPFoxCoordinates (p := p) (d := d) (G := G) where
  toAlgHom := AlgHom.pi fun _ ↦
    (presentationAllFiniteModPCoefficient P).toAlgHom
  cont := continuous_pi fun _ ↦
    (presentationAllFiniteModPCoefficient P).continuous

/-- On a completed group-like element, every diagonal coordinate is the
group-like element of the presentation quotient. -/
@[simp]
theorem presentationAllFiniteModPCoordinateCoefficient_groupLike
    (P : FiniteProPPresentation p d r sourceData G)
    (f : sourceData.carrier) :
    presentationAllFiniteModPCoordinateCoefficient P
        (completedGroupAlgebraOf (ZMod p) sourceData.carrier.obj f) =
      fun _ ↦ completedGroupAlgebraOfInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G (P.quotient f) := by
  funext i
  exact presentationAllFiniteModPCoefficient_groupLike P f

/-- The all-finite continuous linear extension of the mod-`p` presentation
Fox derivative. -/
def presentationAllFiniteCompletedModPFoxOperator
    (P : FiniteProPPresentation p d r sourceData G) :
    CompletedGroupAlgebraCarrier (ZMod p) sourceData.carrier.obj →L[ZMod p]
      PresentationModPFoxCoordinates (p := p) (d := d) (G := G) :=
  completedModPFoxLift
    (G := G) d (presentationModPFoxDerivative P)
    (continuous_presentationModPFoxDerivative P)

/-- The all-finite completed operator restricts to the original group
derivative on completed group-like elements. -/
@[simp]
theorem presentationAllFiniteCompletedModPFoxOperator_groupLike
    (P : FiniteProPPresentation p d r sourceData G)
    (f : sourceData.carrier) :
    presentationAllFiniteCompletedModPFoxOperator P
        (completedGroupAlgebraOf (ZMod p) sourceData.carrier.obj f) =
      presentationModPFoxDerivative P f :=
  completedModPFoxLift_apply_of
    (G := G) d (presentationModPFoxDerivative P)
    (continuous_presentationModPFoxDerivative P) f

/-- The group-like values of the all-finite lift satisfy the crossed-product
law with the diagonal quotient coefficient. -/
theorem presentationAllFiniteCompletedModPFoxOperator_groupLike_crossed
    (P : FiniteProPPresentation p d r sourceData G)
    (f g : sourceData.carrier) :
    presentationAllFiniteCompletedModPFoxOperator P
        (completedGroupAlgebraOf (ZMod p) sourceData.carrier.obj (f * g)) =
      presentationAllFiniteCompletedModPFoxOperator P
          (completedGroupAlgebraOf (ZMod p) sourceData.carrier.obj f) +
        presentationAllFiniteModPCoordinateCoefficient P
            (completedGroupAlgebraOf (ZMod p) sourceData.carrier.obj f) *
          presentationAllFiniteCompletedModPFoxOperator P
            (completedGroupAlgebraOf (ZMod p) sourceData.carrier.obj g) := by
  rw [presentationAllFiniteCompletedModPFoxOperator_groupLike,
    presentationAllFiniteCompletedModPFoxOperator_groupLike,
    presentationAllFiniteCompletedModPFoxOperator_groupLike,
    presentationAllFiniteModPCoordinateCoefficient_groupLike,
    presentationModPFoxDerivative_mul]
  funext i
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]

/-- The all-finite completed mod-`p` Fox operator satisfies the right
Fox--Leibniz rule. -/
theorem presentationAllFiniteCompletedModPFoxOperator_rightLeibniz
    (P : FiniteProPPresentation p d r sourceData G)
    (x y : CompletedGroupAlgebraCarrier (ZMod p) sourceData.carrier.obj) :
    presentationAllFiniteCompletedModPFoxOperator P (x * y) =
      algebraMap (ZMod p)
          (PresentationModPFoxCoordinates (p := p) (d := d) (G := G))
          (allFiniteModPAugmentation (p := p) sourceData.carrier.obj y) *
        presentationAllFiniteCompletedModPFoxOperator P x +
      presentationAllFiniteModPCoordinateCoefficient P x *
        presentationAllFiniteCompletedModPFoxOperator P y := by
  let _ : Algebra (modPProfiniteCommRing p)
      (PresentationModPFoxCoordinates (p := p) (d := d) (G := G)) := by
    change Algebra (ZMod p)
      (PresentationModPFoxCoordinates (p := p) (d := d) (G := G))
    infer_instance
  let _ : ContinuousSMul (modPProfiniteCommRing p)
      (PresentationModPFoxCoordinates (p := p) (d := d) (G := G)) := by
    change ContinuousSMul (ZMod p)
      (PresentationModPFoxCoordinates (p := p) (d := d) (G := G))
    infer_instance
  let _ : T2Space (ModPCompletedGroupAlgebra p G) :=
    completedGroupAlgebraInClass_t2Space
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  let epsilon : CompletedGroupAlgebraCarrier
      (modPProfiniteCommRing p) sourceData.carrier.obj →A[
        modPProfiniteCommRing p] (modPProfiniteCommRing p) := by
    change CompletedGroupAlgebraCarrier (ZMod p) sourceData.carrier.obj →A[
      ZMod p] ZMod p
    exact allFiniteModPAugmentation (p := p) sourceData.carrier.obj
  let phi : CompletedGroupAlgebraCarrier
      (modPProfiniteCommRing p) sourceData.carrier.obj →A[
        modPProfiniteCommRing p]
          PresentationModPFoxCoordinates (p := p) (d := d) (G := G) := by
    change CompletedGroupAlgebraCarrier (ZMod p) sourceData.carrier.obj →A[
      ZMod p] PresentationModPFoxCoordinates (p := p) (d := d) (G := G)
    exact presentationAllFiniteModPCoordinateCoefficient P
  let D : CompletedGroupAlgebraCarrier
      (modPProfiniteCommRing p) sourceData.carrier.obj →L[
        modPProfiniteCommRing p]
          PresentationModPFoxCoordinates (p := p) (d := d) (G := G) := by
    change CompletedGroupAlgebraCarrier (ZMod p) sourceData.carrier.obj →L[
      ZMod p] PresentationModPFoxCoordinates (p := p) (d := d) (G := G)
    exact presentationAllFiniteCompletedModPFoxOperator P
  change D (x * y) =
    algebraMap (modPProfiniteCommRing p)
        (PresentationModPFoxCoordinates (p := p) (d := d) (G := G))
        (epsilon y) * D x + phi x * D y
  exact completedGroupAlgebra_rightFoxLeibniz_of_groupLike
    (modPProfiniteCommRing p) sourceData.carrier.obj epsilon phi D
    (allFiniteModPAugmentation_groupLike
      (p := p) sourceData.carrier.obj)
    (presentationAllFiniteCompletedModPFoxOperator_groupLike_crossed P) x y

/-- After comparison from the pro-`p`-indexed source completion, the
all-finite quotient coefficient is the canonical in-class functorial map. -/
theorem presentationAllFiniteModPCoefficient_fromInClass
    (P : FiniteProPPresentation p d r sourceData G)
    (x : ModPCompletedGroupAlgebra p sourceData.carrier) :
    presentationAllFiniteModPCoefficient P
        (completedGroupAlgebraFromInClass
          (R := ZMod p) (G := sourceData.carrier)
          (FiniteGroupClass.pGroup p)
          (pGroupFullFormation (p := p)).melnikovFormation.formation
          sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass x) =
      modPCompletedGroupAlgebraMap p P.quotient x := by
  have hnat := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraToInClassAlgHom_naturality
        (R := ZMod p) (G := sourceData.carrier) (H := G)
        (FiniteGroupClass.pGroup p)
        (FiniteGroupClass.pGroup_hereditary p)
        P.quotient.toMonoidHom P.quotient.continuous))
    (completedGroupAlgebraFromInClass
      (R := ZMod p) (G := sourceData.carrier)
      (FiniteGroupClass.pGroup p)
      (pGroupFullFormation (p := p)).melnikovFormation.formation
      sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass x)
  change modPCompletedGroupAlgebraMap p P.quotient
      (completedGroupAlgebraToInClass
        (R := ZMod p) (G := sourceData.carrier)
        (FiniteGroupClass.pGroup p)
        (completedGroupAlgebraFromInClass
          (R := ZMod p) (G := sourceData.carrier)
          (FiniteGroupClass.pGroup p)
          (pGroupFullFormation (p := p)).melnikovFormation.formation
          sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass x)) =
    presentationAllFiniteModPCoefficient P
      (completedGroupAlgebraFromInClass
        (R := ZMod p) (G := sourceData.carrier)
        (FiniteGroupClass.pGroup p)
        (pGroupFullFormation (p := p)).melnikovFormation.formation
        sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass x) at hnat
  rw [completedGroupAlgebraToInClass_fromInClass] at hnat
  exact hnat.symm

/-- The diagonal all-finite coefficient likewise becomes the in-class
functorial map in every Fox coordinate. -/
theorem presentationAllFiniteModPCoordinateCoefficient_fromInClass
    (P : FiniteProPPresentation p d r sourceData G)
    (x : ModPCompletedGroupAlgebra p sourceData.carrier) :
    presentationAllFiniteModPCoordinateCoefficient P
        (completedGroupAlgebraFromInClass
          (R := ZMod p) (G := sourceData.carrier)
          (FiniteGroupClass.pGroup p)
          (pGroupFullFormation (p := p)).melnikovFormation.formation
          sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass x) =
      fun _ ↦ modPCompletedGroupAlgebraMap p P.quotient x := by
  funext i
  exact presentationAllFiniteModPCoefficient_fromInClass P x

/-- The all-finite augmentation transported from the free pro-`p` source is
the canonical pro-`p`-indexed augmentation. -/
theorem allFiniteModPAugmentation_fromInClass
    (x : ModPCompletedGroupAlgebra p sourceData.carrier) :
    allFiniteModPAugmentation (p := p) sourceData.carrier.obj
        (completedGroupAlgebraFromInClass
          (R := ZMod p) (G := sourceData.carrier)
          (FiniteGroupClass.pGroup p)
          (pGroupFullFormation (p := p)).melnikovFormation.formation
          sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass x) =
      completedGroupAlgebraCanonicalAugmentationInClass
        (R := ZMod p) (G := sourceData.carrier)
        (FiniteGroupClass.pGroup p) x :=
  completedGroupAlgebraCanonicalAugmentation_fromInClass
    (R := ZMod p) (G := sourceData.carrier)
    (FiniteGroupClass.pGroup p)
    (pGroupFullFormation (p := p)).melnikovFormation.formation
    sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass x

/-- The completed presentation Fox operator on the pro-`p`-indexed source
completion satisfies the right Fox--Leibniz rule. -/
theorem presentationCompletedModPFoxOperator_rightLeibniz
    (P : FiniteProPPresentation p d r sourceData G)
    (x y : ModPCompletedGroupAlgebra p sourceData.carrier) :
    presentationCompletedModPFoxOperator P (x * y) =
      algebraMap (ZMod p)
          (PresentationModPFoxCoordinates (p := p) (d := d) (G := G))
          (completedGroupAlgebraCanonicalAugmentationInClass
            (R := ZMod p) (G := sourceData.carrier)
            (FiniteGroupClass.pGroup p) y) *
        presentationCompletedModPFoxOperator P x +
      (fun _ ↦ modPCompletedGroupAlgebraMap p P.quotient x) *
        presentationCompletedModPFoxOperator P y := by
  let C := FiniteGroupClass.pGroup p
  let hForm := (pGroupFullFormation (p := p)).melnikovFormation.formation
  let hF := sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass
  let Φ := completedGroupAlgebraFromInClassRingHom
    (R := ZMod p) (G := sourceData.carrier) C hForm hF
  have hall := presentationAllFiniteCompletedModPFoxOperator_rightLeibniz
    P (Φ x) (Φ y)
  have hepsilon :
      allFiniteModPAugmentation (p := p) sourceData.carrier.obj (Φ y) =
        completedGroupAlgebraCanonicalAugmentationInClass
          (R := ZMod p) (G := sourceData.carrier)
          (FiniteGroupClass.pGroup p) y := by
    dsimp [Φ, C, hForm, hF]
    exact allFiniteModPAugmentation_fromInClass y
  have hphi :
      presentationAllFiniteModPCoordinateCoefficient P (Φ x) =
        fun _ ↦ modPCompletedGroupAlgebraMap p P.quotient x := by
    dsimp [Φ, C, hForm, hF]
    exact presentationAllFiniteModPCoordinateCoefficient_fromInClass P x
  rw [hepsilon, hphi] at hall
  change presentationAllFiniteCompletedModPFoxOperator P (Φ (x * y)) = _
  rw [Φ.map_mul]
  exact hall

end

end ClassFieldTower.ProP
