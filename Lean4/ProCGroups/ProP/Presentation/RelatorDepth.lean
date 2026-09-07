import ProCGroups.ProP.Presentation.Minimal
import ProCGroups.ProP.Zassenhaus.Depth

set_option autoImplicit false
/-!
# Zassenhaus depth of displayed relators

The relation-depth interface reuses the group-level predicate-valued depth.
Minimality supplies degree two directly from the identified
power--commutator core, without choosing a finite maximum for an element of
infinite depth.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups

noncomputable section

universe u

namespace FiniteProPPresentation

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The displayed `i`-th relator has Zassenhaus depth at least `n`. -/
def RelatorZassenhausDepthAtLeast
    (P : FiniteProPPresentation p d r sourceData G)
    (n : ℕ) (i : Fin r) : Prop :=
  ZassenhausDepthAtLeast p n (P.relator i)

/-- Relator depth is exactly completed augmentation-power membership of its
group-like difference. -/
theorem relatorZassenhausDepthAtLeast_iff
    (P : FiniteProPPresentation p d r sourceData G)
    (n : ℕ) (i : Fin r) :
    P.RelatorZassenhausDepthAtLeast n i ↔
      groupLikeDifference p sourceData.carrier (P.relator i) ∈
        closedAugmentationPower p sourceData.carrier n :=
  Iff.rfl

/-- A lower depth bound for a relator can be weakened. -/
theorem relatorZassenhausDepthAtLeast_mono
    (P : FiniteProPPresentation p d r sourceData G)
    {m n : ℕ} (hmn : m ≤ n) {i : Fin r}
    (hi : P.RelatorZassenhausDepthAtLeast n i) :
    P.RelatorZassenhausDepthAtLeast m i :=
  zassenhausDepthAtLeast_mono p hmn hi

/-- Every displayed relator of a minimal presentation has depth at least
two. -/
theorem relatorZassenhausDepthAtLeast_two
    (P : FiniteProPPresentation p d r sourceData G)
    (hP : P.IsMinimal) (i : Fin r) :
    P.RelatorZassenhausDepthAtLeast 2 i :=
  closedPowerCommutator_le_zassenhausSubgroup_two p sourceData.carrier
    (P.relator_mem_closedPowerCommutator hP i)

end FiniteProPPresentation

end


end ClassFieldTower.ProP
