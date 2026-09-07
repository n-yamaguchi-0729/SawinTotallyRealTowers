import ProCGroups.InverseSystems.FiniteStageFactorization
import ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation

set_option autoImplicit false
/-!
# Finite-stage factorization of continuous maps

Every continuous map from a pro-`C` group to a finite discrete space factors through one of the
canonical open-normal quotients in `C`.  This is the finite-stage input for reducing continuous
finite-coefficient cochains to finite quotients.
-/

open scoped Topology

namespace ClassFieldTower.Cohomology

open ProCGroups ProCGroups.ProC ProCGroups.InverseSystems

universe u w

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every continuous map from a pro-`C` group to a finite discrete space factors through one
open-normal quotient in `C`. -/
theorem exists_openNormalSubgroupInClass_factor_continuousMap_finite
    [CompactSpace G] [T2Space G]
    (hForm : FiniteGroupClass.Formation C)
    (hG : HasOpenNormalBasisInClass C G)
    {Y : Type w} [TopologicalSpace Y] [Finite Y] [DiscreteTopology Y]
    (rho : G → Y) (hrho : Continuous rho) :
    ∃ U : OpenNormalSubgroupInClass C G,
      ∃ rhoU : (G ⧸ (U.1 : Subgroup G)) → Y,
        Continuous rhoU ∧
          rho = rhoU ∘ OpenNormalSubgroupInClass.quotientProj U := by
  let _ : Nonempty Y := ⟨rho 1⟩
  let S := openNormalSubgroupInClassSystem C G
  let e : G ≃ₜ* S.inverseLimit :=
    HasOpenNormalBasisInClass.openNormalSubgroupInClassMulEquivInverseLimit hForm hG
  let _ : Nonempty (OpenNormalSubgroupInClass C G) :=
    HasOpenNormalBasisInClass.openNormalSubgroupInClass_nonempty hG
  let _ : ∀ U : OrderDual (OpenNormalSubgroupInClass C G), Finite (S.X U) := fun U => by
    dsimp [S, openNormalSubgroupInClassSystem]
    exact openNormalSubgroup_finiteQuotient (G := G) (OrderDual.ofDual U).1
  let _ : ∀ U : OrderDual (OpenNormalSubgroupInClass C G), DiscreteTopology (S.X U) :=
    fun U => by
      dsimp [S, openNormalSubgroupInClassSystem]
      exact QuotientGroup.discreteTopology
        (openNormalSubgroup_isOpen (G := G) (OrderDual.ofDual U).1)
  have hdir : Directed (· ≤ ·)
      (id : OrderDual (OpenNormalSubgroupInClass C G) →
        OrderDual (OpenNormalSubgroupInClass C G)) :=
    directed_openNormalSubgroupInClass hForm
  have hcont : Continuous (rho ∘ e.symm) := hrho.comp e.symm.continuous
  obtain ⟨k, rhoK, hrhoK, hfac⟩ :=
    S.factors_through_projection_finite hdir (rho ∘ e.symm) hcont
  refine ⟨OrderDual.ofDual k, rhoK, hrhoK, ?_⟩
  funext g
  have hk :=
    HasOpenNormalBasisInClass.openNormalSubgroupInClassMulEquivInverseLimit_projection
      hForm hG k g
  have hfacg := congrFun hfac (e g)
  change rho g = rhoK (OpenNormalSubgroupInClass.quotientProj (OrderDual.ofDual k) g)
  calc
    rho g = (rho ∘ e.symm) (e g) := by simp [e]
    _ = rhoK (S.projection k (e g)) := hfacg
    _ = rhoK (OpenNormalSubgroupInClass.quotientProj (OrderDual.ofDual k) g) := by
      rw [hk]
      rfl

end ClassFieldTower.Cohomology
