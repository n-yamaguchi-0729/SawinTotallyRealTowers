import ProCGroups.ProP.Fox.ModPGroupDerivative
import ProCGroups.CompletedGroupAlgebra.UniversalProperty.ProfiniteModule
import ProCGroups.CompletedGroupAlgebra.InClassFunctoriality.Comparison

set_option autoImplicit false
/-!
# Completed mod-p Fox operators

The continuous mod-`p` Fox derivative on a free pro-`p` group extends uniquely
to its completed group algebra.  The resulting continuous linear map is then
transported from the all-finite completion to the `p`-group-indexed model used
by the Zassenhaus filtration.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open ProCGroups

noncomputable section

universe u

/-- `ZMod p`, with its finite discrete topology, as a bundled profinite
commutative coefficient ring. -/
def modPProfiniteCommRing (p : ℕ) [Fact p.Prime] : ProfiniteCommRing where
  toProfinite := Profinite.of (ZMod p)
  commRing := inferInstance
  isTopologicalRing := inferInstance

/-- A finite row of mod-`p` completed group algebras as a profinite module over
`ZMod p`. -/
def modPFoxCoordinatesProfiniteModule
    (p d : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ProfiniteModule.{0, u} (modPProfiniteCommRing p).toProfiniteRing := by
  letI : CompactSpace (ModPCompletedGroupAlgebra p G) :=
    completedGroupAlgebraInClass_compactSpace
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  letI : T2Space (ModPCompletedGroupAlgebra p G) :=
    completedGroupAlgebraInClass_t2Space
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  letI : TotallyDisconnectedSpace (ModPCompletedGroupAlgebra p G) :=
    completedGroupAlgebraInClass_totallyDisconnectedSpace
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
  exact
    { toProfinite :=
        Profinite.of (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G)
      addCommGroup := inferInstance
      module := by
        change Module (ZMod p)
          (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G)
        infer_instance
      isTopologicalAddGroup := inferInstance
      continuousSMul := by
        change ContinuousSMul (ZMod p)
          (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G)
        infer_instance }

variable {p : ℕ} [Fact p.Prime]
variable {F G : Type u}
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [TotallyDisconnectedSpace F]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The unique continuous `ZMod p`-linear extension of a continuous map from
a profinite group to a finite row of mod-`p` completed group algebras. -/
def completedModPFoxLift
    (d : ℕ)
    (f : F → (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G))
    (hf : Continuous f) :
    CompletedGroupAlgebraCarrier (ZMod p) F →L[ZMod p]
      (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G) := by
  have h := completedGroupAlgebraOf_hasFreeLiftTo
    (modPProfiniteCommRing p) (ProfiniteGrp.of F)
    (modPFoxCoordinatesProfiniteModule p d G)
  change ∀ f : F → (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G),
    Continuous f →
    ∃! L : CompletedGroupAlgebraCarrier (ZMod p) F →L[ZMod p]
      (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G),
      ∀ g : F, L (completedGroupAlgebraOf (ZMod p) F g) = f g at h
  exact Classical.choose (h f hf)

/-- The all-finite completed lift agrees with its input on group-like
elements. -/
@[simp]
theorem completedModPFoxLift_apply_of
    (d : ℕ)
    (f : F → (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G))
    (hf : Continuous f) (g : F) :
    completedModPFoxLift (G := G) d f hf
        (completedGroupAlgebraOf (ZMod p) F g) =
      f g := by
  have h := completedGroupAlgebraOf_hasFreeLiftTo
    (modPProfiniteCommRing p) (ProfiniteGrp.of F)
    (modPFoxCoordinatesProfiniteModule p d G)
  change ∀ f : F → (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G),
    Continuous f →
    ∃! L : CompletedGroupAlgebraCarrier (ZMod p) F →L[ZMod p]
      (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G),
      ∀ g : F, L (completedGroupAlgebraOf (ZMod p) F g) = f g at h
  exact (Classical.choose_spec (h f hf)).1 g

/-- Precompose the all-finite completed lift with the comparison map from the
`p`-group-indexed completed group algebra. -/
def completedModPFoxInClassLift
    (d : ℕ)
    (hF : ProC.HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) F)
    (f : F → (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G))
    (hf : Continuous f) :
    ModPCompletedGroupAlgebra p F →L[ZMod p]
      (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G) := by
  exact show
      ModPCompletedGroupAlgebra p F →L[ZMod p]
        (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G) from
    { toFun := fun x =>
        completedModPFoxLift (G := G) d f hf
          (completedGroupAlgebraFromInClass
            (R := ZMod p) (G := F)
            (FiniteGroupClass.pGroup p)
            (pGroupFullFormation (p := p)).melnikovFormation.formation hF x)
      map_add' := by
        intro x y
        let Φ := completedGroupAlgebraFromInClassRingHom
          (R := ZMod p) (G := F) (FiniteGroupClass.pGroup p)
          (pGroupFullFormation (p := p)).melnikovFormation.formation hF
        calc
          completedModPFoxLift (G := G) d f hf
                (completedGroupAlgebraFromInClass
                  (R := ZMod p) (G := F) (FiniteGroupClass.pGroup p)
                  (pGroupFullFormation (p := p)).melnikovFormation.formation hF (x + y)) =
              completedModPFoxLift (G := G) d f hf (Φ x + Φ y) :=
            congrArg (completedModPFoxLift (G := G) d f hf) (Φ.map_add x y)
          _ = _ := (completedModPFoxLift (G := G) d f hf).map_add (Φ x) (Φ y)
      map_smul' := by
        intro c x
        let Φ := completedGroupAlgebraFromInClassAlgHom
          (R := ZMod p) (G := F) (FiniteGroupClass.pGroup p)
          (pGroupFullFormation (p := p)).melnikovFormation.formation hF
        calc
          completedModPFoxLift (G := G) d f hf
                (completedGroupAlgebraFromInClass
                  (R := ZMod p) (G := F) (FiniteGroupClass.pGroup p)
                  (pGroupFullFormation (p := p)).melnikovFormation.formation hF (c • x)) =
              completedModPFoxLift (G := G) d f hf (c • Φ x) :=
            congrArg (completedModPFoxLift (G := G) d f hf)
              (Φ.toLinearMap.map_smul c x)
          _ = _ := (completedModPFoxLift (G := G) d f hf).map_smul c (Φ x)
      cont :=
        (completedModPFoxLift (G := G) d f hf).continuous.comp
          (continuous_completedGroupAlgebraFromInClass
            (R := ZMod p) (G := F)
            (FiniteGroupClass.pGroup p)
            (pGroupFullFormation (p := p)).melnikovFormation.formation hF) }

/-- The class-indexed completed lift agrees with its input on group-like
elements. -/
@[simp]
theorem completedModPFoxInClassLift_apply_of
    (d : ℕ)
    (hF : ProC.HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) F)
    (f : F → (ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G))
    (hf : Continuous f) (g : F) :
    completedModPFoxInClassLift (G := G) d hF f hf
        (completedGroupAlgebraOfInClass
          (FiniteGroupClass.pGroup p) (ZMod p) F g) =
      f g := by
  change completedModPFoxLift (G := G) d f hf
      (completedGroupAlgebraFromInClass
        (R := ZMod p) (G := F) (FiniteGroupClass.pGroup p)
        (pGroupFullFormation (p := p)).melnikovFormation.formation hF
        (completedGroupAlgebraOfInClass
          (FiniteGroupClass.pGroup p) (ZMod p) F g)) = f g
  rw [completedGroupAlgebraFromInClass_of]
  exact completedModPFoxLift_apply_of (G := G) d f hf g

variable {d r : ℕ}
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The continuous completed mod-`p` Fox operator attached to a finite pro-`p`
presentation. -/
def presentationCompletedModPFoxOperator
    (P : FiniteProPPresentation p d r sourceData G) :
    ModPCompletedGroupAlgebra p sourceData.carrier →L[ZMod p]
      PresentationModPFoxCoordinates (p := p) (d := d) (G := G) :=
  completedModPFoxInClassLift
    (G := G) d sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass
    (presentationModPFoxDerivative P)
    (continuous_presentationModPFoxDerivative P)

/-- On completed group-like elements, the completed operator is the original
mod-`p` presentation Fox derivative. -/
@[simp]
theorem presentationCompletedModPFoxOperator_apply_groupLike
    (P : FiniteProPPresentation p d r sourceData G)
    (f : sourceData.carrier) :
    presentationCompletedModPFoxOperator
        (p := p) (d := d) (r := r) (sourceData := sourceData) (G := G) P
        (completedGroupAlgebraOfInClass
          (FiniteGroupClass.pGroup p) (ZMod p) sourceData.carrier f) =
      presentationModPFoxDerivative P f :=
  completedModPFoxInClassLift_apply_of
    (G := G) d sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass
    (presentationModPFoxDerivative P)
    (continuous_presentationModPFoxDerivative P) f

end

end ClassFieldTower.ProP
