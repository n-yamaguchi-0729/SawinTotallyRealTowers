import ProCGroups.FreeProC.FiniteBasis
import ProCGroups.Presentations.Profinite

set_option autoImplicit false
/-!
# Finite pro-p presentations

This leaf packages an actual finite free pro-`p` source, a displayed finite
relator family, and the existing `IsFreePresentationOf` certificate.  The free
source data is a type index, rather than a structure field, so its canonical
group and topology instances remain syntactically determined.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups
open ProCGroups.Presentations

noncomputable section

universe u

/-- A finite pro-`p` presentation with `d` generators and `r` displayed
relators. -/
structure FiniteProPPresentation
    (p d r : ℕ) [Fact p.Prime]
    (sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p))
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] where
  /-- The chosen free basis has cardinality `d`. -/
  basisCard : Cardinal.mk sourceData.basis = d
  /-- The displayed family of `r` relators in the free source. -/
  relator : Fin r → sourceData.carrier
  /-- The quotient is the closed normal quotient by the displayed relators. -/
  isPresentation :
    IsFreePresentationOf
      (X := ULift.{u} (Fin d))
      (F := sourceData.carrier)
      (G := G)
      (FiniteGroupClass.pGroup p)
      (CrowellExactSequence.freeProCChosenULiftFamilyOfBasisCard
        sourceData basisCard)
      (Set.range relator)

namespace FiniteProPPresentation

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The canonical quotient map selected by the underlying presentation. -/
def quotient (P : FiniteProPPresentation p d r sourceData G) :
    sourceData.carrier →ₜ* G :=
  P.isPresentation.π

/-- The presentation quotient is surjective. -/
theorem quotient_surjective (P : FiniteProPPresentation p d r sourceData G) :
    Function.Surjective P.quotient :=
  P.isPresentation.π_surjective

/-- The kernel is the closed normal closure of the displayed relators. -/
theorem kernel_eq_closedNormalClosure
    (P : FiniteProPPresentation p d r sourceData G) :
    P.quotient.toMonoidHom.ker = closedNormalClosure (Set.range P.relator) :=
  P.isPresentation.kernel_eq_closedNormalClosure

/-- The target has a pro-`p` open-normal basis. -/
theorem targetProP (P : FiniteProPPresentation p d r sourceData G) :
    ProC.HasPGroupOpenNormalBasis p G :=
  P.isPresentation.targetProC

/-- Every displayed relator lies in the presentation kernel. -/
theorem relator_mem_kernel
    (P : FiniteProPPresentation p d r sourceData G) (i : Fin r) :
    P.relator i ∈ P.quotient.toMonoidHom.ker := by
  rw [P.kernel_eq_closedNormalClosure]
  exact subset_closedNormalClosure (Set.range P.relator) ⟨i, rfl⟩

end FiniteProPPresentation

end


end ClassFieldTower.ProP
