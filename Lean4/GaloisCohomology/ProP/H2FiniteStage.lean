import GaloisCohomology.ProP.H2FiniteStageCochain

set_option autoImplicit false
/-!
# Finite-stage realization of continuous degree-two classes

Every lifted degree-two class of a pro-`p` group is inflated from a finite `p`-group quotient.
-/

open scoped Topology

namespace ClassFieldTower.Cohomology

open CategoryTheory TopRep ContRepresentation
open ProCGroups ProCGroups.ProC
open H2FiniteStageAux

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Every lifted degree-two class of a pro-`p` group is inflated from one finite `p`-group
quotient. -/
theorem exists_openNormalSubgroupInClass_inflation_eq_degree_two
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G)
    (x : continuousCohomologyZModPLifted p G 2) :
    ∃ U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G,
      ∃ xU : continuousCohomologyZModPLifted p
          (G ⧸ (U.1 : Subgroup G)) 2,
        continuousCohomologyZModPMapLifted p
          (OpenNormalSubgroupInClass.quotientProj U) 2 xU = x := by
  let z := ProP.PresentationH2Aux.targetCocycleSection x
  have hPi : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) (Triple G) :=
    HasOpenNormalBasisInClass.pi (α := Coordinate) (β := fun _ => G)
      (FiniteGroupClass.pGroup_formation p) (fun _ => hG)
  obtain ⟨W, rhoW, _hrhoW, hfac⟩ :=
    exists_openNormalSubgroupInClass_factor_continuousMap_finite
      (FiniteGroupClass.pGroup_formation p) hPi
      (cocycleTupleMap z) (cocycleTupleMap_continuous z)
  let U := commonCoordinateSubgroup W
  have heq (a b : Triple G)
      (hab : ∀ i : Fin 3,
        OpenNormalSubgroupInClass.quotientProj U (a (coordinateIndex i)) =
          OpenNormalSubgroupInClass.quotientProj U (b (coordinateIndex i))) :
      cocycleTupleMap z a = cocycleTupleMap z b :=
    map_eq_of_coordinate_quotients W (cocycleTupleMap z) rhoW hfac a b hab
  let Q := G ⧸ (U.1 : Subgroup G)
  let : DiscreteTopology Q :=
    QuotientGroup.discreteTopology (openNormalSubgroup_isOpen (G := G) U.1)
  let cU : (trivialZModPCochainsLifted p Q).X 2 :=
    descendedHomogeneousCochain W z heq
  have hcU : ((trivialZModPCochainsLifted p Q).d 2 3).hom cU = 0 :=
    descendedHomogeneousCochain_mem_cycles W z heq
  let zU : trivialZModPCocyclesLifted p Q 2 :=
    homogeneousCocycleOfElement (trivialZModPLifted p Q) 2 cU hcU
  have hpullCochain :
      ((trivialZModPCochainsMapLifted p
        (OpenNormalSubgroupInClass.quotientProj U)).f 2).hom cU =
        ((trivialZModPCochainsLifted p G).iCycles 2).hom z := by
    apply Subtype.ext
    ext a b c
    change cocycleTupleMap z
        (triple (quotientSection U (OpenNormalSubgroupInClass.quotientProj U a))
          (quotientSection U (OpenNormalSubgroupInClass.quotientProj U b))
          (quotientSection U (OpenNormalSubgroupInClass.quotientProj U c))) =
      cocycleTupleMap z (triple a b c)
    apply heq
    intro i
    fin_cases i
    · simpa [triple, coordinateIndex] using
        quotientProj_quotientSection_proj U a
    · simpa [triple, coordinateIndex] using
        quotientProj_quotientSection_proj U b
    · simpa [triple, coordinateIndex] using
        quotientProj_quotientSection_proj U c
  have hpullCycle :
      trivialZModPCocyclesMapLifted p
          (OpenNormalSubgroupInClass.quotientProj U) 2 zU = z := by
    apply topModule_mono_injective_lifted ((trivialZModPCochainsLifted p G).iCycles 2)
    calc
      _ = ((trivialZModPCochainsMapLifted p
          (OpenNormalSubgroupInClass.quotientProj U)).f 2).hom
            (((trivialZModPCochainsLifted p Q).iCycles 2).hom zU) := by
        exact ConcreteCategory.congr_hom
          (HomologicalComplex.cyclesMap_i
            (trivialZModPCochainsMapLifted p
              (OpenNormalSubgroupInClass.quotientProj U)) 2) zU
      _ = ((trivialZModPCochainsMapLifted p
          (OpenNormalSubgroupInClass.quotientProj U)).f 2).hom cU := by
        rw [iCycles_homogeneousCocycleOfElement]
      _ = _ := hpullCochain
  refine ⟨U, ContinuousCohomology.π (trivialZModPLifted p Q) 2 zU, ?_⟩
  have hnat := ConcreteCategory.congr_hom
    (trivialZModPLifted_π_naturality p
      (OpenNormalSubgroupInClass.quotientProj U) 2) zU
  calc
    continuousCohomologyZModPMapLifted p
        (OpenNormalSubgroupInClass.quotientProj U) 2
        (ContinuousCohomology.π (trivialZModPLifted p Q) 2 zU) =
      ContinuousCohomology.π (trivialZModPLifted p G) 2
        (trivialZModPCocyclesMapLifted p
          (OpenNormalSubgroupInClass.quotientProj U) 2 zU) := hnat
    _ = ContinuousCohomology.π (trivialZModPLifted p G) 2 z := by rw [hpullCycle]
    _ = x := ProP.PresentationH2Aux.targetCocycleSection_π x

end

end ClassFieldTower.Cohomology
