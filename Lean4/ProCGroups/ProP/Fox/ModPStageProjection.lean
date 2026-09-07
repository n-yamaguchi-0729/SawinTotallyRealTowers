import ProCGroups.ProP.Fox.ModPFiniteStage
import ProCGroups.ProP.Fox.ModPDisplayedSpan

set_option autoImplicit false
/-!
# Mod-p completed-to-finite Fox stage projection

A finite p-group quotient of the presented group gives a canonical projection from the
mod-p completed group algebra to the reflected finite Fox target.  This module constructs
the coefficient and coordinate projections, proves compatibility with the completed and
finite Fox boundaries, and identifies projected presentation derivatives with the reflected
finite-stage derivative on abstract free words.
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

/-- The selected quotient coordinate of the mod-`p` completed group algebra. -/
def presentationModPFiniteStageProjection
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    ModPCompletedGroupAlgebra p G →+*
      CompletedGroupAlgebraStageInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G (OrderDual.toDual ⟨U, hU⟩) :=
  completedGroupAlgebraProjectionInClass
    (FiniteGroupClass.pGroup p) (ZMod p) G (OrderDual.toDual ⟨U, hU⟩)

/-- The reflected comparison, typed at the selected completed-algebra quotient index. -/
def presentationModPFiniteStageQMapAtIndex
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    FoxDifferential.CompletedGroupAlgebraQuotientInClass G (FiniteGroupClass.pGroup p)
        (OrderDual.toDual ⟨U, hU⟩) →*
      presentationModPFiniteStageTarget P U hU :=
  presentationModPFiniteStageQMap P U hU

/-- Change the quotient support from `G/U` to the reflected finite Fox target. -/
def presentationModPFiniteStageQMapAlgebra
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    CompletedGroupAlgebraStageInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G (OrderDual.toDual ⟨U, hU⟩) →+*
      foxAlgebraicStageTargetGroupAlgebra
        (presentationModPFiniteStageKernel P U hU) p :=
  MonoidAlgebra.mapDomainRingHom (ZMod p)
    (presentationModPFiniteStageQMapAtIndex P U hU)

/-- The actual coefficient projection from the completed algebra to the reflected stage. -/
def presentationModPFiniteStageCoefficientMap
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    ModPCompletedGroupAlgebra p G →+*
      foxAlgebraicStageTargetGroupAlgebra
        (presentationModPFiniteStageKernel P U hU) p :=
  (presentationModPFiniteStageQMapAlgebra P U hU).comp
    (presentationModPFiniteStageProjection U hU)

/-- Apply the coefficient projection in every Fox coordinate. -/
def presentationModPFiniteStageCoordinateMap
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    PresentationModPFoxCoordinates (p := p) (d := d) (G := G) →+
      foxAlgebraicStageCoordinateVector
        (presentationModPFiniteStageKernel P U hU) p where
  toFun v i := presentationModPFiniteStageCoefficientMap P U hU (v i)
  map_zero' := by
    funext i
    exact map_zero _
  map_add' v w := by
    funext i
    exact map_add _ _ _

@[simp]
theorem presentationModPFiniteStageCoordinateMap_apply
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G))
    (i : ULift.{u} (Fin d)) :
    presentationModPFiniteStageCoordinateMap P U hU v i =
      presentationModPFiniteStageCoefficientMap P U hU (v i) :=
  rfl

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp]
theorem presentationModPFiniteStageProjection_of
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (g : G) :
    presentationModPFiniteStageProjection U hU
        (completedGroupAlgebraOfInClass
          (FiniteGroupClass.pGroup p) (ZMod p) G g) =
      MonoidAlgebra.of (ZMod p)
        (FoxDifferential.CompletedGroupAlgebraQuotientInClass G (FiniteGroupClass.pGroup p)
          (OrderDual.toDual ⟨U, hU⟩))
        (QuotientGroup.mk g) := by
  exact completedGroupAlgebraProjectionInClass_of
    (ZMod p) G (FiniteGroupClass.pGroup p) (OrderDual.toDual ⟨U, hU⟩) g

theorem presentationModPFiniteStageCoefficientMap_groupLike
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (g : G) :
    presentationModPFiniteStageCoefficientMap P U hU
        (completedGroupAlgebraOfInClass
          (FiniteGroupClass.pGroup p) (ZMod p) G g) =
      MonoidAlgebra.of (ZMod p)
        (presentationModPFiniteStageTarget P U hU)
        (presentationModPFiniteStageQMapAtIndex P U hU
          (QuotientGroup.mk g)) := by
  rw [presentationModPFiniteStageCoefficientMap, RingHom.comp_apply,
    presentationModPFiniteStageProjection_of,
    presentationModPFiniteStageQMapAlgebra]
  exact finiteGroupAlgebra_mapDomainRingHom_of
    (ZMod p)
    (FoxDifferential.CompletedGroupAlgebraQuotientInClass G
      (FiniteGroupClass.pGroup p) (OrderDual.toDual ⟨U, hU⟩))
    (presentationModPFiniteStageTarget P U hU)
    (presentationModPFiniteStageQMapAtIndex P U hU)
    (QuotientGroup.mk g)

@[simp]
theorem presentationModPFiniteStageQMapAtIndex_generator
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (i : ULift.{u} (Fin d)) :
    presentationModPFiniteStageQMapAtIndex P U hU
        (QuotientGroup.mk (P.quotient (presentationChosenGenerator P i))) =
      QuotientGroup.mk'
        (presentationModPFiniteStageKernel P U hU) (FreeGroup.of i) := by
  exact presentationModPFiniteStageQMap_generator P U hU i

theorem presentationModPFiniteStageCoefficientMap_chosenGenerator
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (i : ULift.{u} (Fin d)) :
    presentationModPFiniteStageCoefficientMap P U hU
        (groupLikeDifference p G
          (P.quotient (presentationChosenGenerator P i))) =
      MonoidAlgebra.of (ZMod p)
          (presentationModPFiniteStageTarget P U hU)
          (QuotientGroup.mk'
            (presentationModPFiniteStageKernel P U hU) (FreeGroup.of i)) - 1 := by
  rw [groupLikeDifference, map_sub, map_one,
    presentationModPFiniteStageCoefficientMap_groupLike,
    presentationModPFiniteStageQMapAtIndex_generator]

/-- The completed mod-`p` presentation boundary commutes with the reflected stage projection. -/
theorem presentationModPFiniteStageFoxBoundary_coordinateMap
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G)) :
    foxAlgebraicStageFoxBoundary
        (presentationModPFiniteStageKernel P U hU) p
        (presentationModPFiniteStageCoordinateMap P U hU v) =
      presentationModPFiniteStageCoefficientMap P U hU
        (presentationModPFoxBoundary P v) := by
  rw [foxAlgebraicStageFoxBoundary_apply,
    presentationModPFoxBoundary_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [presentationModPFiniteStageCoordinateMap_apply, map_mul,
    presentationModPFiniteStageCoefficientMap_chosenGenerator]

/-- The integral completed coefficient map attached to the same reflected stage. -/
def presentationZCFiniteStageCoefficientMap
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G →+*
      foxAlgebraicStageTargetGroupAlgebra
        (presentationModPFiniteStageKernel P U hU) p :=
  zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap
    (presentationModPFiniteStageKernel P U hU) p
    (modPCoefficientIndex p, OrderDual.toDual ⟨U, hU⟩) dvd_rfl
    (presentationModPFiniteStageQMapAtIndex P U hU)

/-- The selected quotient followed by the reflected target comparison. -/
def presentationModPFiniteStageRightMap
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G))) :
    G →* presentationModPFiniteStageTarget P U hU :=
  (presentationModPFiniteStageQMapAtIndex P U hU).comp
    (openNormalSubgroupInClassProj
      (C := FiniteGroupClass.pGroup p) (G := G)
      (OrderDual.toDual ⟨U, hU⟩))

@[simp]
theorem presentationZCFiniteStageCoefficientMap_groupLike
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (g : G) :
    presentationZCFiniteStageCoefficientMap P U hU
        (zcGroupLike (FiniteGroupClass.pGroup p) G g) =
      MonoidAlgebra.of (ZMod p)
        (presentationModPFiniteStageTarget P U hU)
        (presentationModPFiniteStageRightMap P U hU g) := by
  exact zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap_groupLike_eq_stageRight
    (presentationModPFiniteStageKernel P U hU) p
    (modPCoefficientIndex p, OrderDual.toDual ⟨U, hU⟩) dvd_rfl
    (presentationModPFiniteStageQMapAtIndex P U hU)
    (presentationModPFiniteStageRightMap P U hU) (fun _ ↦ rfl) g

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp]
theorem presentationModPFiniteStageProjection_reduction
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (x : ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G) :
    presentationModPFiniteStageProjection U hU
        (modPCoefficientReduction p G x) =
      zcCompletedGroupAlgebraProjection
        (FiniteGroupClass.pGroup p) G
        (modPCoefficientIndex p, OrderDual.toDual ⟨U, hU⟩) x := by
  exact completedGroupAlgebraProjectionInClass_modPCoefficientReduction
    p G (OrderDual.toDual ⟨U, hU⟩) x

/-- Reducing coefficients modulo `p` and then taking the selected stage is the
same coefficient map as the integral completed stage with modulus `p`. -/
theorem presentationModPFiniteStageCoefficientMap_reduction
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (x : ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G) :
    presentationModPFiniteStageCoefficientMap P U hU
        (modPCoefficientReduction p G x) =
      presentationZCFiniteStageCoefficientMap P U hU x := by
  have hmodP :
      p ∣ (modPCoefficientIndex p :
        ProCGroups.Completion.ProCIntegerIndex
          (FiniteGroupClass.pGroup p : FiniteGroupClass.{u})).modulus := by
    simpa only [modPCoefficientIndex_modulus] using Nat.dvd_refl p
  let stageIndex : ZCCompletedGroupAlgebraIndex
      (FiniteGroupClass.pGroup p) G :=
    (modPCoefficientIndex p, OrderDual.toDual ⟨U, hU⟩)
  let : Fact (0 < stageIndex.1.modulus) := ⟨stageIndex.1.positive⟩
  have hstageSelf :
      zcCompletedGroupAlgebraStageToFoxAlgebraicStage
          (presentationModPFiniteStageKernel P U hU) stageIndex.1.modulus
          stageIndex dvd_rfl
          (presentationModPFiniteStageQMapAtIndex P U hU) =
        MonoidAlgebra.mapDomainRingHom
          (ModNCompletedCoeff stageIndex.1.modulus)
          (presentationModPFiniteStageQMapAtIndex P U hU) := by
    apply MonoidAlgebra.ringHom_ext
    · intro a
      rw [zcCompletedGroupAlgebraStageToFoxAlgebraicStage_single]
      rw [modNCompletedCoeffMap_rfl, RingHom.id_apply,
        MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, map_one]
    · intro q
      rw [← MonoidAlgebra.of_apply,
        zcCompletedGroupAlgebraStageToFoxAlgebraicStage_of]
      rw [MonoidAlgebra.mapDomainRingHom_apply]
      change MonoidAlgebra.single _ 1 =
        MonoidAlgebra.mapDomain _ (MonoidAlgebra.single _ 1)
      exact MonoidAlgebra.mapDomain_single.symm
  have hstageP :
      zcCompletedGroupAlgebraStageToFoxAlgebraicStage
          (presentationModPFiniteStageKernel P U hU) p
          (modPCoefficientIndex p, OrderDual.toDual ⟨U, hU⟩) hmodP
          (presentationModPFiniteStageQMapAtIndex P U hU) =
        MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff p)
          (presentationModPFiniteStageQMapAtIndex P U hU) := by
    exact Eq.mp (by rfl) hstageSelf
  rw [presentationModPFiniteStageCoefficientMap, RingHom.comp_apply,
    presentationModPFiniteStageProjection_reduction,
    presentationModPFiniteStageQMapAlgebra,
    presentationZCFiniteStageCoefficientMap,
    zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap_apply
      (n := p)
      (i := (modPCoefficientIndex p, OrderDual.toDual ⟨U, hU⟩))
      (hmod := hmodP)
      (qmap := presentationModPFiniteStageQMapAtIndex P U hU),
    hstageP]
  rfl

@[simp]
theorem presentationModPFiniteStageRightMap_generator
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (i : ULift.{u} (Fin d)) :
    presentationModPFiniteStageRightMap P U hU
        (P.quotient (presentationChosenGenerator P i)) =
      QuotientGroup.mk'
        (presentationModPFiniteStageKernel P U hU) (FreeGroup.of i) := by
  exact presentationModPFiniteStageQMap_generator P U hU i

/-- Exact instantiation of the generic completed-to-finite derivative compatibility theorem. -/
theorem presentationZCFiniteStageDerivative_word
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (w : FreeGroup (ULift.{u} (Fin d))) :
    zcFreeFoxCoordinatesStageMap
        (presentationModPFiniteStageKernel P U hU) p
        (presentationZCFiniteStageCoefficientMap P U hU)
        (zcFreeGroupFoxDerivativeVector (FiniteGroupClass.pGroup p)
          (FreeGroup.lift (fun i ↦
            P.quotient (presentationChosenGenerator P i))) w) =
      foxAlgebraicStageDerivativeVector
        (presentationModPFiniteStageKernel P U hU) p w := by
  exact zcFreeFoxCoordinatesStageMap_derivativeVector_of_generators
    (presentationModPFiniteStageKernel P U hU) p
    (fun i ↦ P.quotient (presentationChosenGenerator P i))
    (presentationZCFiniteStageCoefficientMap P U hU)
    (presentationModPFiniteStageRightMap P U hU)
    (presentationZCFiniteStageCoefficientMap_groupLike P U hU)
    (presentationModPFiniteStageRightMap_generator P U hU) w

/-- Restricting the completed presentation derivative to abstract words recovers
the completed free-group derivative. -/
theorem presentationFoxDerivative_word
    (P : FiniteProPPresentation p d r sourceData G)
    (w : FreeGroup (ULift.{u} (Fin d))) :
    presentationFoxDerivative P
        (FreeGroup.lift (presentationChosenGenerator P) w) =
      zcFreeGroupFoxDerivativeVector (FiniteGroupClass.pGroup p)
        (FreeGroup.lift (fun i ↦
          P.quotient (presentationChosenGenerator P i))) w := by
  let ι : ULift.{u} (Fin d) → sourceData.carrier :=
    presentationChosenGenerator P
  let ρ : sourceData.carrier →* G := P.quotient.toMonoidHom
  let D := presentationFoxDerivative P
  let δ : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar
        (FiniteGroupClass.pGroup p) (ρ.comp (FreeGroup.lift ι)))
      (PresentationFoxCoordinates (p := p) (d := d) (G := G)) :=
    { toFun := fun w ↦ D (FreeGroup.lift ι w)
      map_mul' := by
        intro a b
        simpa [ρ, D] using
          (presentationFoxDerivative P).map_mul
            (FreeGroup.lift ι a) (FreeGroup.lift ι b) }
  have hbasis : ∀ i : ULift.{u} (Fin d),
      δ (FreeGroup.of i) =
        Pi.single i (1 : PresentationFoxCoefficientRing (p := p) (G := G)) := by
    intro i
    change D (FreeGroup.lift ι (FreeGroup.of i)) = _
    rw [FreeGroup.lift_apply_of]
    exact presentationFoxDerivative_chosenGenerator P i
  have hδ : δ =
      zcFreeGroupFoxDerivativeVector
        (FiniteGroupClass.pGroup p) (ρ.comp (FreeGroup.lift ι)) :=
    zcFreeGroupFoxDerivativeVector_unique
      (FiniteGroupClass.pGroup p) (ρ.comp (FreeGroup.lift ι)) δ hbasis
  have hρlift : ρ.comp (FreeGroup.lift ι) =
      FreeGroup.lift (fun i ↦ P.quotient (presentationChosenGenerator P i)) := by
    ext i
    simp [ρ, ι]
  have hw := congrArg
    (fun E : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar
        (FiniteGroupClass.pGroup p) (ρ.comp (FreeGroup.lift ι)))
      (PresentationFoxCoordinates (p := p) (d := d) (G := G)) ↦ E w) hδ
  change D (FreeGroup.lift ι w) =
    zcFreeGroupFoxDerivativeVector
      (FiniteGroupClass.pGroup p) (ρ.comp (FreeGroup.lift ι)) w at hw
  rw [← hρlift]
  simpa [D, ι] using hw

/-- The integral presentation derivative projects to the reflected finite derivative on words. -/
theorem presentationZCFiniteStageDerivative_presentationWord
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (w : FreeGroup (ULift.{u} (Fin d))) :
    zcFreeFoxCoordinatesStageMap
        (presentationModPFiniteStageKernel P U hU) p
        (presentationZCFiniteStageCoefficientMap P U hU)
        (presentationFoxDerivative P
          (FreeGroup.lift (presentationChosenGenerator P) w)) =
      foxAlgebraicStageDerivativeVector
        (presentationModPFiniteStageKernel P U hU) p w := by
  rw [presentationFoxDerivative_word]
  exact presentationZCFiniteStageDerivative_word P U hU w

/-- The mod-`p` presentation derivative projects coordinatewise to the
reflected finite-stage derivative on abstract words. -/
theorem presentationModPFiniteStageDerivative_presentationWord
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (w : FreeGroup (ULift.{u} (Fin d))) :
    presentationModPFiniteStageCoordinateMap P U hU
        (presentationModPFoxDerivative P
          (FreeGroup.lift (presentationChosenGenerator P) w)) =
      foxAlgebraicStageDerivativeVector
        (presentationModPFiniteStageKernel P U hU) p w := by
  rw [← presentationFoxCoordinatesModPReduction_derivative]
  calc
    presentationModPFiniteStageCoordinateMap P U hU
        (presentationFoxCoordinatesModPReduction (p := p) (G := G)
          (presentationFoxDerivative P
            (FreeGroup.lift (presentationChosenGenerator P) w))) =
      zcFreeFoxCoordinatesStageMap
        (presentationModPFiniteStageKernel P U hU) p
        (presentationZCFiniteStageCoefficientMap P U hU)
        (presentationFoxDerivative P
          (FreeGroup.lift (presentationChosenGenerator P) w)) := by
      funext i
      rw [presentationModPFiniteStageCoordinateMap_apply,
        presentationFoxCoordinatesModPReduction_apply,
        zcFreeFoxCoordinatesStageMap_apply,
        presentationModPFiniteStageCoefficientMap_reduction]
    _ = foxAlgebraicStageDerivativeVector
        (presentationModPFiniteStageKernel P U hU) p w :=
      presentationZCFiniteStageDerivative_presentationWord P U hU w

end

end ClassFieldTower.ProP
