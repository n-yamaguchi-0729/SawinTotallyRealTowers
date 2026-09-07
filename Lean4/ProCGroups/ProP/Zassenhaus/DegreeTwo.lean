import ProCGroups.ProP.GeneratorRank
import ProCGroups.ProP.Zassenhaus.Basic
import ProCGroups.ProP.Zassenhaus.FiniteDegreeOne

set_option autoImplicit false
/-!
# The second Zassenhaus subgroup

For a topologically finitely generated pro-`p` group, the closed
power--commutator subgroup is open.  Projection to this finite elementary
quotient detects a degree-two completed augmentation relation.  The finite
degree-one criterion then gives the reverse inclusion to the elementary
power--commutator subgroup, complementing the inclusion proved in `Basic`.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open ProCGroups.Generation
open ProCGroups.FiniteGeneration

noncomputable section

universe u

variable (p : ℕ) [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The closed power--commutator subgroup, bundled as an open normal subgroup
when the ambient group is topologically finitely generated. -/
def closedPowerCommutatorOpenNormal
    (hfg : TopologicallyFinitelyGenerated G) : OpenNormalSubgroup G := by
  letI : (closedPowerCommutator p G).Normal :=
    closedPowerCommutator_normal p G
  letI : IsClosed (closedPowerCommutator p G : Set G) :=
    isClosed_closedPowerCommutator p G
  letI : Finite (powerCommutatorQuotient p G) :=
    powerCommutatorQuotient_finite_of_topologicallyFinitelyGenerated hfg
  letI : DiscreteTopology (powerCommutatorQuotient p G) :=
    Finite.instDiscreteTopology
  exact
    { toOpenSubgroup :=
        { toSubgroup := closedPowerCommutator p G
          isOpen' := by
            have hopenker : IsOpen
                (((powerCommutatorQuotientMk p G).ker : Subgroup G) : Set G) := by
              change IsOpen
                ((powerCommutatorQuotientMk p G) ⁻¹'
                  ({1} : Set (powerCommutatorQuotient p G)))
              exact (isOpen_discrete _).preimage
                (powerCommutatorQuotientMk p G).continuous_toFun
            rw [← ker_powerCommutatorQuotientMk]
            exact hopenker }
      isNormal' := closedPowerCommutator_normal p G }

/-- A completed degree-two augmentation relation forces membership in the
closed power--commutator subgroup. -/
theorem mem_closedPowerCommutator_of_groupLikeDifference_mem_degree_two
    (hpG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G)
    (hfg : TopologicallyFinitelyGenerated G) (g : G)
    (hg : groupLikeDifference p G g ∈ closedAugmentationPower p G 2) :
    g ∈ closedPowerCommutator p G := by
  let Uopen : OpenNormalSubgroup G := closedPowerCommutatorOpenNormal p hfg
  have hUopen : ((Uopen : OpenNormalSubgroup G) : Subgroup G) =
      closedPowerCommutator p G := by
    rfl
  let : (closedPowerCommutator p G).Normal :=
    closedPowerCommutator_normal p G
  have hQU := ProCGroups.ProC.HasOpenNormalBasisInClass.quotient_mem
    (ProCGroups.FiniteGroupClass.pGroup_formation p) hpG Uopen
  let Uclass : ProCGroups.ProC.OpenNormalSubgroupInClass
      (ProCGroups.FiniteGroupClass.pGroup p) G := ⟨Uopen, hQU⟩
  let U : CompletedGroupAlgebraIndexInClass G
      (ProCGroups.FiniteGroupClass.pGroup p) := OrderDual.toDual Uclass
  let Qstage := CompletedGroupAlgebraQuotientInClass G
    (ProCGroups.FiniteGroupClass.pGroup p) U
  let : Finite Qstage := by
    dsimp [Qstage, U, Uclass]
    exact hQU.1
  let : DiscreteTopology Qstage := by
    dsimp [Qstage, U, Uclass]
    exact QuotientGroup.discreteTopology
      (ProCGroups.openNormalSubgroup_isOpen (G := G) Uopen)
  let : TopologicalSpace (MonoidAlgebra (ZMod p) Qstage) :=
    (completedGroupAlgebraSystemInClass
      (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G).topologicalSpace U
  let : Finite (MonoidAlgebra (ZMod p) Qstage) :=
    finite_completedGroupAlgebraStageInClass
      (R := ZMod p) (G := G) (ProCGroups.FiniteGroupClass.pGroup p) U
  let : T2Space (MonoidAlgebra (ZMod p) Qstage) :=
    finiteGroupAlgebra_t2Space (ZMod p) Qstage
  let pr : ModPCompletedGroupAlgebra p G →+* MonoidAlgebra (ZMod p) Qstage :=
    completedGroupAlgebraProjectionInClass
      (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G U
  let J : Ideal (MonoidAlgebra (ZMod p) Qstage) :=
    groupAlgebraAugmentationIdeal (ZMod p) Qstage
  have hproj : pr
        (completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g - 1) ∈ J ^ 2 := by
    change completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g - 1 ∈
        closedAugmentationPower p G 2 at hg
    unfold closedAugmentationPower at hg
    change completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g - 1 ∈
        closure ((((modPAugmentationIdeal p G) ^ 2 :
          Ideal (ModPCompletedGroupAlgebra p G))) : Set _) at hg
    have hcont : Continuous pr :=
      continuous_completedGroupAlgebraProjectionInClass
        (R := ZMod p) (G := G) (ProCGroups.FiniteGroupClass.pGroup p) U
    have hclosed : IsClosed
        ((J ^ 2 : Ideal (MonoidAlgebra (ZMod p) Qstage)) :
          Set (MonoidAlgebra (ZMod p) Qstage)) :=
      ((J ^ 2 : Ideal (MonoidAlgebra (ZMod p) Qstage)) :
        Set (MonoidAlgebra (ZMod p) Qstage)).toFinite.isClosed
    have hclosure := map_mem_closure
      (f := pr)
      (s := (((modPAugmentationIdeal p G) ^ 2 :
        Ideal (ModPCompletedGroupAlgebra p G)) : Set _))
      (t := ((J ^ 2 : Ideal (MonoidAlgebra (ZMod p) Qstage)) :
        Set (MonoidAlgebra (ZMod p) Qstage))) hcont hg (by
        intro x hx
        apply ringHom_mem_ideal_pow pr (J := J) (n := 2) (x := x) (by
          intro y hy
          change groupAlgebraAugmentation (ZMod p) Qstage (pr y) = 0
          change completedGroupAlgebraStageAugmentationInClass
            (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G U (pr y) = 0
          have heq := congrArg
            (fun f : ModPCompletedGroupAlgebra p G →+* ZMod p => f y)
            (completedGroupAlgebraStageAugmentationInClass_comp_projectionInClass
              (R := ZMod p) (G := G)
              (ProCGroups.FiniteGroupClass.pGroup p) U)
          change completedGroupAlgebraStageAugmentationInClass
                (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G U (pr y) =
              completedGroupAlgebraCanonicalAugmentationInClass
                (R := ZMod p) (G := G)
                (ProCGroups.FiniteGroupClass.pGroup p) y at heq
          rw [heq]
          exact hy) hx)
    rwa [hclosed.closure_eq] at hclosure
  let q : Qstage :=
    QuotientGroup.mk' ((Uopen : OpenNormalSubgroup G) : Subgroup G) g
  have hgen : groupAlgebraAugmentationGenerator (ZMod p) Qstage q ∈ J ^ 2 := by
    change MonoidAlgebra.of (ZMod p) Qstage q - 1 ∈ J ^ 2
    have hof : pr
          (completedGroupAlgebraOfInClass
            (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g) =
        MonoidAlgebra.of (ZMod p) Qstage q := by
      dsimp [pr]
      rw [completedGroupAlgebraProjectionInClass_of]
      rfl
    rw [map_sub, map_one, hof] at hproj
    exact hproj
  have hfrattini : q ∈ frattini Qstage := by
    have hQstage : IsPGroup p Qstage := by
      dsimp [Qstage, U, Uclass]
      exact hQU.2
    exact
      (groupAlgebraAugmentationGenerator_mem_sq_iff_mem_frattini p
        Qstage hQstage q).1 hgen
  have hfrattiniBot : frattini Qstage = ⊥ := by
    have hQstage : IsPGroup p Qstage := hQU.2
    rw [frattini_eq_closedPowerCommutator_of_isPGroup hQstage]
    let fstage : G →ₜ* Qstage := by
      dsimp [Qstage, U, Uclass]
      exact ProCGroups.ProC.OpenNormalSubgroup.quotientProj Uopen
    rw [← closedPowerCommutator_map_eq_of_surjective_finite fstage (by
      change Function.Surjective
        (ProCGroups.ProC.OpenNormalSubgroup.quotientProj Uopen)
      exact ProCGroups.ProC.OpenNormalSubgroup.quotientProj_surjective Uopen)]
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      change fstage x = 1
      have hxU : x ∈ ((Uopen : OpenNormalSubgroup G) : Subgroup G) := by
        rw [hUopen]
        exact hx
      have hxeq : QuotientGroup.mk'
          ((Uopen : OpenNormalSubgroup G) : Subgroup G) x = 1 :=
        (QuotientGroup.eq_one_iff
          (N := ((Uopen : OpenNormalSubgroup G) : Subgroup G)) x).2 hxU
      change (ProCGroups.ProC.OpenNormalSubgroup.quotientProj Uopen) x = 1
      exact hxeq
    · exact bot_le
  rw [hfrattiniBot] at hfrattini
  change q = 1 at hfrattini
  dsimp [q] at hfrattini
  have hgU : g ∈ ((Uopen : OpenNormalSubgroup G) : Subgroup G) :=
    (QuotientGroup.eq_one_iff
      (N := ((Uopen : OpenNormalSubgroup G) : Subgroup G)) g).mp hfrattini
  rw [hUopen] at hgU
  exact hgU

/-- The second Zassenhaus subgroup is contained in the closed
power--commutator subgroup for a finitely generated pro-`p` group. -/
theorem zassenhausSubgroup_two_le_closedPowerCommutator
    (hpG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G)
    (hfg : TopologicallyFinitelyGenerated G) :
    zassenhausSubgroup p G 2 ≤ closedPowerCommutator p G := by
  intro g hg
  exact mem_closedPowerCommutator_of_groupLikeDifference_mem_degree_two p hpG hfg g hg

/-- The second Zassenhaus subgroup is the closed subgroup generated by
`p`-th powers and commutators. -/
theorem zassenhausSubgroup_two_eq_closedPowerCommutator
    (hpG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G)
    (hfg : TopologicallyFinitelyGenerated G) :
    zassenhausSubgroup p G 2 = closedPowerCommutator p G :=
  le_antisymm (zassenhausSubgroup_two_le_closedPowerCommutator p hpG hfg)
    (closedPowerCommutator_le_zassenhausSubgroup_two p G)

end

end ClassFieldTower.ProP
