import ProCGroups.ProP.Fox.ModPDisplayedSpan
import ProCGroups.ProP.Fox.ModPStageProjection

set_option autoImplicit false
/-!
# Completed mod-p Fox density and relation exactness

Finite reflected Fox exactness supplies a matching presentation word at every
finite `p`-group quotient.  The corresponding matching subsets of the compact
free pro-`p` source are nonempty, closed, and directed under refinement.
Compactness therefore produces one source element matching all completed
coefficient coordinates and all target quotients.  Separation identifies it as
an actual presentation-kernel element whose mod-`p` Fox derivative is the
given boundary cycle.

Combining this density result with the displayed-row span theorem proves
unfiltered exactness of the completed relation matrix followed by the Fox
boundary.
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

/-- The reflected right projection sends a presentation word to its finite
quotient class. -/
theorem presentationModPFiniteStageRightMap_presentationWord
    (P : FiniteProPPresentation p d r sourceData G)
    (U : OpenNormalSubgroup G)
    (hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)))
    (w : FreeGroup (ULift.{u} (Fin d))) :
    presentationModPFiniteStageRightMap P U hU
        (P.quotient (FreeGroup.lift (presentationChosenGenerator P) w)) =
      QuotientGroup.mk' (presentationModPFiniteStageKernel P U hU) w := by
  induction w using FreeGroup.induction_on with
  | C1 => simp only [map_one]
  | of i =>
      rw [FreeGroup.lift_apply_of]
      exact presentationModPFiniteStageRightMap_generator P U hU i
  | inv_of i hi => simpa only [map_inv] using congrArg Inv.inv hi
  | mul a b ha hb => simp only [map_mul, ha, hb]

/-- Raw finite-stage equality conditions on a possible lift of a completed
boundary cycle. -/
def presentationModPFiniteStageMatchSet
    (P : FiniteProPPresentation p d r sourceData G)
    (v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G))
    (j : CompletedGroupAlgebra.CompletedGroupAlgebraIndexInClass G
      (FiniteGroupClass.pGroup p)) :
    Set sourceData.carrier :=
  {f |
    (∀ i : ULift.{u} (Fin d),
      completedGroupAlgebraProjectionInClass
          (FiniteGroupClass.pGroup p) (ZMod p) G j
          (presentationModPFoxDerivative P f i) =
        completedGroupAlgebraProjectionInClass
          (FiniteGroupClass.pGroup p) (ZMod p) G j (v i)) ∧
    openNormalSubgroupInClassProj
        (C := FiniteGroupClass.pGroup p) (G := G) j (P.quotient f) = 1}

/-- Finite-stage exactness produces a presentation word matching a completed
boundary cycle at every raw coefficient and target quotient coordinate. -/
theorem presentationModPFiniteStageMatchSet_nonempty
    (P : FiniteProPPresentation p d r sourceData G)
    (v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G))
    (hv : presentationModPFoxBoundary P v = 0)
    (j : CompletedGroupAlgebra.CompletedGroupAlgebraIndexInClass G
      (FiniteGroupClass.pGroup p)) :
    (presentationModPFiniteStageMatchSet P v j).Nonempty := by
  let U : OpenNormalSubgroup G := (OrderDual.ofDual j).1
  have hU : FiniteGroupClass.pGroup p (G ⧸ (U : Subgroup G)) :=
    (OrderDual.ofDual j).2
  have hvcycle :
      presentationModPFiniteStageCoordinateMap P U hU v ∈
        foxAlgebraicStageBoundaryCycleSubmodule
          (presentationModPFiniteStageKernel P U hU) p := by
    change foxAlgebraicStageFoxBoundary
      (presentationModPFiniteStageKernel P U hU) p
      (presentationModPFiniteStageCoordinateMap P U hU v) = 0
    rw [presentationModPFiniteStageFoxBoundary_coordinateMap, hv, map_zero]
  have hcovered :
      foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel
        (X := ULift.{u} (Fin d))
        (presentationModPFiniteStageKernel P U hU) p :=
    foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel_of_relationBoundaryExact
      (X := ULift.{u} (Fin d))
      (presentationModPFiniteStageKernel P U hU) p
      (presentationModPFiniteStageRelationBoundaryExact P U hU)
  have hwords :=
    (foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel_iff_words
      (X := ULift.{u} (Fin d))
      (N := presentationModPFiniteStageKernel P U hU) (n := p)).1
      hcovered hvcycle
  rcases hwords with ⟨w, hwN, hwderiv⟩
  refine ⟨FreeGroup.lift (presentationChosenGenerator P) w, ?_, ?_⟩
  · intro i
    have hQinj : Function.Injective
        (presentationModPFiniteStageQMapAlgebra P U hU) := by
      change Function.Injective (MonoidAlgebra.mapDomain
        (R := ZMod p) (presentationModPFiniteStageQMapAtIndex P U hU))
      exact MonoidAlgebra.mapDomain_injective
        (presentationModPFiniteStageQMap_injective P U hU)
    apply hQinj
    have hcoord := congrFun
      (presentationModPFiniteStageDerivative_presentationWord P U hU w) i
    have hwordi := congrFun hwderiv i
    exact hcoord.trans hwordi
  · have hQinj := presentationModPFiniteStageQMap_injective P U hU
    apply hQinj
    rw [map_one]
    change presentationModPFiniteStageRightMap P U hU
        (P.quotient (FreeGroup.lift (presentationChosenGenerator P) w)) = 1
    rw [presentationModPFiniteStageRightMap_presentationWord]
    exact (QuotientGroup.eq_one_iff
      (N := presentationModPFiniteStageKernel P U hU) w).2 hwN

/-- Each raw finite-stage matching condition is closed in the compact free
pro-`p` source. -/
theorem isClosed_presentationModPFiniteStageMatchSet
    (P : FiniteProPPresentation p d r sourceData G)
    (v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G))
    (j : CompletedGroupAlgebra.CompletedGroupAlgebraIndexInClass G
      (FiniteGroupClass.pGroup p)) :
    IsClosed (presentationModPFiniteStageMatchSet P v j) := by
  let : TopologicalSpace
      (CompletedGroupAlgebraStageInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G j) :=
    (completedGroupAlgebraSystemInClass
      (FiniteGroupClass.pGroup p) (ZMod p) G).topologicalSpace j
  let : Finite
      (CompletedGroupAlgebra.CompletedGroupAlgebraQuotientInClass G
        (FiniteGroupClass.pGroup p) j) :=
    finite_completedGroupAlgebraQuotientInClass G (FiniteGroupClass.pGroup p) j
  let : DiscreteTopology
      (CompletedGroupAlgebraStageInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G j) :=
    finiteGroupAlgebraTopology_discrete_of_discrete_coeff (ZMod p)
      (CompletedGroupAlgebra.CompletedGroupAlgebraQuotientInClass G
        (FiniteGroupClass.pGroup p) j)
  let : TopologicalSpace
      (CompletedGroupAlgebra.CompletedGroupAlgebraQuotientInClass G
        (FiniteGroupClass.pGroup p) j) := ⊥
  let : DiscreteTopology
      (CompletedGroupAlgebra.CompletedGroupAlgebraQuotientInClass G
        (FiniteGroupClass.pGroup p) j) := ⟨rfl⟩
  have hleft : IsClosed
      (⋂ i : ULift.{u} (Fin d),
      {f : sourceData.carrier |
        completedGroupAlgebraProjectionInClass
            (FiniteGroupClass.pGroup p) (ZMod p) G j
            (presentationModPFoxDerivative P f i) =
          completedGroupAlgebraProjectionInClass
            (FiniteGroupClass.pGroup p) (ZMod p) G j (v i)}) := by
    apply isClosed_iInter
    intro i
    apply isClosed_eq
    · exact (continuous_completedGroupAlgebraProjectionInClass
        (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p) j).comp
        ((continuous_apply i).comp (continuous_presentationModPFoxDerivative P))
    · exact continuous_const
  have hright : IsClosed
      {f : sourceData.carrier |
        openNormalSubgroupInClassProj
            (C := FiniteGroupClass.pGroup p) (G := G) j (P.quotient f) = 1} := by
    apply isClosed_eq
    · have hproj : Continuous
          (openNormalSubgroupInClassProj
            (C := FiniteGroupClass.pGroup p) (G := G) j) := by
        change Continuous (QuotientGroup.mk'
          (((OrderDual.ofDual j).1 : OpenNormalSubgroup G) : Subgroup G))
        exact continuous_quotient_mk'
      exact hproj.comp P.quotient.continuous
    · exact continuous_const
  simpa only [presentationModPFiniteStageMatchSet, Set.ofPred_and,
    Set.ofPred_forall] using hleft.inter hright

/-- Matching at a finer raw quotient stage implies matching at every coarser
stage. -/
theorem presentationModPFiniteStageMatchSet_anti
    (P : FiniteProPPresentation p d r sourceData G)
    (v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G))
    {j k : CompletedGroupAlgebra.CompletedGroupAlgebraIndexInClass G
      (FiniteGroupClass.pGroup p)} (hjk : j ≤ k) :
    presentationModPFiniteStageMatchSet P v k ⊆
      presentationModPFiniteStageMatchSet P v j := by
  intro f hf
  rcases hf with ⟨hcoeff, hright⟩
  constructor
  · intro i
    calc
      completedGroupAlgebraProjectionInClass
          (FiniteGroupClass.pGroup p) (ZMod p) G j
          (presentationModPFoxDerivative P f i) =
        completedGroupAlgebraTransitionInClass
          (FiniteGroupClass.pGroup p) (ZMod p) G hjk
          (completedGroupAlgebraProjectionInClass
            (FiniteGroupClass.pGroup p) (ZMod p) G k
            (presentationModPFoxDerivative P f i)) :=
          (completedGroupAlgebraProjectionInClass_compatible
            (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p) hjk _).symm
      _ = completedGroupAlgebraTransitionInClass
          (FiniteGroupClass.pGroup p) (ZMod p) G hjk
          (completedGroupAlgebraProjectionInClass
            (FiniteGroupClass.pGroup p) (ZMod p) G k (v i)) := by
          rw [hcoeff i]
      _ = completedGroupAlgebraProjectionInClass
          (FiniteGroupClass.pGroup p) (ZMod p) G j (v i) :=
          completedGroupAlgebraProjectionInClass_compatible
            (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p) hjk _
  · let transition := OpenNormalSubgroupInClass.map
      (C := FiniteGroupClass.pGroup p) (G := G)
      (U := OrderDual.ofDual j) (V := OrderDual.ofDual k) hjk
    calc
      openNormalSubgroupInClassProj
          (C := FiniteGroupClass.pGroup p) (G := G) j (P.quotient f) =
        transition (openNormalSubgroupInClassProj
          (C := FiniteGroupClass.pGroup p) (G := G) k (P.quotient f)) :=
          (congrFun (openNormalSubgroupInClassProj_compatible
            (C := FiniteGroupClass.pGroup p) (G := G) j k hjk)
            (P.quotient f)).symm
      _ = transition 1 := by rw [hright]
      _ = 1 := map_one transition

/-- Every completed mod-`p` boundary cycle is the Fox derivative of an
actual presentation-kernel element. -/
theorem exists_presentationKernel_of_presentationModPFoxBoundary_eq_zero
    (P : FiniteProPPresentation p d r sourceData G)
    (v : PresentationModPFoxCoordinates (p := p) (d := d) (G := G))
    (hv : presentationModPFoxBoundary P v = 0) :
    ∃ f : sourceData.carrier,
      P.quotient f = 1 ∧ presentationModPFoxDerivative P f = v := by
  let J := CompletedGroupAlgebra.CompletedGroupAlgebraIndexInClass G
    (FiniteGroupClass.pGroup p)
  let : Nonempty J :=
    OpenNormalSubgroupInClass.nonempty_of_containsTrivialQuotients
      (C := FiniteGroupClass.pGroup p) (G := G)
  have hJdir : Directed (· ≤ ·) (id : J → J) :=
    directed_openNormalSubgroupInClass
      (G := G) (FiniteGroupClass.pGroup_formation p)
  have hsetsDir : Directed (· ⊇ ·)
      (fun j : J ↦ presentationModPFiniteStageMatchSet P v j) := by
    intro j k
    rcases hJdir j k with ⟨l, hjl, hkl⟩
    exact ⟨l,
      presentationModPFiniteStageMatchSet_anti P v hjl,
      presentationModPFiniteStageMatchSet_anti P v hkl⟩
  have hclosed : ∀ j : J,
      IsClosed (presentationModPFiniteStageMatchSet P v j) :=
    fun j ↦ isClosed_presentationModPFiniteStageMatchSet P v j
  have hcompact : ∀ j : J,
      IsCompact (presentationModPFiniteStageMatchSet P v j) :=
    fun j ↦ (hclosed j).isCompact
  have hnonempty : ∀ j : J,
      (presentationModPFiniteStageMatchSet P v j).Nonempty :=
    fun j ↦ presentationModPFiniteStageMatchSet_nonempty P v hv j
  rcases IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun j : J ↦ presentationModPFiniteStageMatchSet P v j)
      hsetsDir hnonempty hcompact hclosed with ⟨f, hf⟩
  rw [Set.mem_iInter] at hf
  refine ⟨f, ?_, ?_⟩
  · apply (P.targetProP).eq_of_forall_openNormalSubgroupInClassProj_eq
    intro j
    simpa only [map_one] using (hf j).2
  · funext i
    apply completedGroupAlgebraInClass_ext
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
    intro j
    exact (hf j).1 i

/-- Unfiltered exactness of the completed relation matrix followed by the
mod-`p` Fox boundary. -/
theorem presentationModPRelationMatrix_boundary_exact
    (P : FiniteProPPresentation p d r sourceData G) :
    Function.Exact (presentationModPRelationMatrix P)
      (presentationModPFoxBoundary P) := by
  intro v
  constructor
  · intro hv
    rcases exists_presentationKernel_of_presentationModPFoxBoundary_eq_zero
      P v hv with ⟨f, hfker, hfderiv⟩
    let n : P.quotient.toMonoidHom.ker := ⟨f, hfker⟩
    have hn := presentationModPFoxDerivative_mem_relationMatrix_range P n
    rw [hfderiv] at hn
    exact hn
  · rintro ⟨a, rfl⟩
    have hcomp := congrArg
      (fun L : (Fin r → ModPCompletedGroupAlgebra p G) →ₗ[
        ModPCompletedGroupAlgebra p G] ModPCompletedGroupAlgebra p G ↦ L a)
      (presentationModPFoxBoundary_comp_relationMatrix P)
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hcomp

end

end ClassFieldTower.ProP
