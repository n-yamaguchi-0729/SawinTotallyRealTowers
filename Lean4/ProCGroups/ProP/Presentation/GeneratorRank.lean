import ProCGroups.ProP.GeneratorRank
import ProCGroups.ProP.Presentation.Minimal

set_option autoImplicit false
/-!
# Generator rank of a minimal pro-p presentation

The displayed free basis gives the upper rank bound.  Minimality supplies a
surjection from the target to the source Frattini quotient, and the Burnside
basis theorem lifts a small generating set back to the free source, giving the
reverse bound.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups
open ProCGroups.FiniteGeneration
open ProCGroups.Generation
open ProCGroups.Presentations

noncomputable section

universe u

namespace FiniteProPPresentation

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

local instance : (closedPowerCommutator p sourceData.carrier).Normal :=
  closedPowerCommutator_normal p sourceData.carrier

/-- The displayed free basis gives an at-most-`d` generating family of the
target. -/
theorem target_topologicallyGeneratedByAtMost
    (P : FiniteProPPresentation p d r sourceData G) :
    TopologicallyGeneratedByAtMost (G := G) d := by
  classical
  let family : ULift.{u} (Fin d) → sourceData.carrier :=
    CrowellExactSequence.freeProCChosenULiftFamilyOfBasisCard
      sourceData P.basisCard
  let imageFamily : ULift.{u} (Fin d) → G := fun i => P.quotient (family i)
  have hgen : TopologicallyGenerates (G := G) (Set.range imageFamily) := by
    simpa [family, imageFamily, quotient] using
      CrowellExactSequence.freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (C := FiniteGroupClass.pGroup p)
        sourceData P.basisCard P.quotient P.quotient_surjective
  refine ⟨Finset.univ.image imageFamily, ?_, ?_⟩
  · exact (Finset.card_image_le).trans_eq (by
      simp only [Finset.card_univ, Fintype.card_ulift, Fintype.card_fin])
  · simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using hgen

/-- The free source has the displayed generator rank. -/
theorem source_topologicalRank_eq_nat
    (P : FiniteProPPresentation p d r sourceData G) :
    topologicalRank sourceData.carrier = d := by
  classical
  let e : sourceData.basis ≃ Fin d :=
    Classical.choice ((Cardinal.mk_eq_nat_iff).1 P.basisCard)
  let _ : Finite sourceData.basis := Finite.of_injective e e.injective
  have hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        FiniteGroupClass.pGroup p A ∧ IsCyclic A ∧ Nontrivial A := by
    refine ⟨ULift.{u} (Multiplicative (ZMod p)), inferInstance,
      inferInstance, ?_⟩
    refine ⟨⟨inferInstance, ?_⟩, ?_, inferInstance⟩
    · exact IsPGroup.of_card (n := 1) (by simp)
    · exact (MulEquiv.ulift (α := Multiplicative (ZMod p))).isCyclic.mpr
        inferInstance
  have hsource :=
    FreeProC.basisCard_eq_topologicalRank_of_finiteBasis
      (FiniteGroupClass.pGroup p)
      (FiniteGroupClass.pGroup_formation p).quotientClosed
      hcyc sourceData
  exact hsource.symm.trans P.basisCard

/-- Minimality forces the target generator rank to equal the displayed free
rank. -/
theorem target_topologicalRank_eq_nat
    (P : FiniteProPPresentation p d r sourceData G) (hP : P.IsMinimal) :
    topologicalRank G = d := by
  classical
  have hAtD : TopologicallyGeneratedByAtMost (G := G) d :=
    P.target_topologicallyGeneratedByAtMost
  have hRankLe : topologicalRank G ≤ (d : Cardinal) :=
    topologicalRank_le_of_topologicallyGeneratedByAtMost hAtD
  have hRankLt : topologicalRank G < Cardinal.aleph0 :=
    hRankLe.trans_lt Cardinal.natCast_lt_aleph0
  let n : ℕ := Cardinal.toNat (topologicalRank G)
  have hCast : (n : Cardinal) = topologicalRank G :=
    Cardinal.cast_toNat_of_lt_aleph0 hRankLt
  have hAtN : TopologicallyGeneratedByAtMost (G := G) n :=
    topologicallyGeneratedByAtMost_of_topologicalRank_eq_nat hCast.symm
  have hQAtN :
      TopologicallyGeneratedByAtMost
        (G := powerCommutatorQuotient p sourceData.carrier) n :=
    TopologicallyGeneratedByAtMost.of_surjective
      (P.targetToSourcePowerCommutatorQuotient hP)
      (P.targetToSourcePowerCommutatorQuotient_surjective hP) hAtN
  rcases hQAtN with ⟨s, hsCard, hsGen⟩
  let liftQ : powerCommutatorQuotient p sourceData.carrier →
      sourceData.carrier :=
    Function.surjInv
      (powerCommutatorQuotientMk_surjective p sourceData.carrier)
  let t : Finset sourceData.carrier := s.image liftQ
  have hFAtN : TopologicallyGeneratedByAtMost
      (G := sourceData.carrier) n := by
    refine ⟨t, Finset.card_image_le.trans hsCard, ?_⟩
    apply
      (topologicallyGenerates_iff_powerCommutatorQuotient_image
        sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass).2
    have himage :
        powerCommutatorQuotientMk p sourceData.carrier ''
            (t : Set sourceData.carrier) =
          (s : Set (powerCommutatorQuotient p sourceData.carrier)) := by
      ext y
      simp [t, liftQ, Function.surjInv_eq]
    rw [himage]
    exact hsGen
  have hdle : (d : Cardinal) ≤ (n : Cardinal) := by
    rw [← P.source_topologicalRank_eq_nat]
    exact topologicalRank_le_of_topologicallyGeneratedByAtMost hFAtN
  apply le_antisymm hRankLe
  exact hdle.trans_eq hCast

/-- Natural-valued generator-rank form of
`target_topologicalRank_eq_nat`. -/
theorem target_topologicalGeneratorRank_eq
    (P : FiniteProPPresentation p d r sourceData G) (hP : P.IsMinimal) :
    topologicalGeneratorRank G = d := by
  rw [topologicalGeneratorRank, P.target_topologicalRank_eq_nat hP]
  simp

end FiniteProPPresentation

end


end ClassFieldTower.ProP
