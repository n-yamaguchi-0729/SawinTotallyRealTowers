import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteLimit.System

set_option autoImplicit false

/-!
# Completed Group Algebra / Open Finite Quotient Topology / Open Finite Limit / Topology

This module transports the discrete topological-ring structures of the open-finite quotient stages
through the single two-parameter inverse limit, and records compactness and separation results.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v

variable (R : Type u) [CommRing R] [TopologicalSpace R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    Ring ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := by
  change Ring (CompletedGroupAlgebraOpenQuotientStage R G K)
  infer_instance

/-- Each two-parameter finite quotient stage is a topological ring for its discrete topology. -/
theorem completedGroupAlgebraOpenFiniteQuotientStage_isTopologicalRing
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    letI : TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    IsTopologicalRing (CompletedGroupAlgebraOpenQuotientStage R G K) := by
  let : TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  have : DiscreteTopology (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    completedGroupAlgebraOpenFiniteQuotientStage_discrete R G K
  infer_instance

/-- Each open-finite quotient stage is finite for compact topological coefficients. -/
theorem completedGroupAlgebraOpenFiniteQuotientStage_fintype
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [IsTopologicalRing R] [CompactSpace R]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    Nonempty (Fintype (CompletedGroupAlgebraOpenQuotientStage R G K)) := by
  classical
  let I : Ideal R := (OrderDual.ofDual K.1).1
  have hIopen : IsOpen (I : Set R) := (OrderDual.ofDual K.1).2
  rcases finite_quotient_of_openIdeal R I hIopen with ⟨hIfin⟩
  let : Fintype (R ⧸ I) := hIfin
  let : Fintype (CompletedGroupAlgebraQuotient G K.2) :=
    Fintype.ofFinite (CompletedGroupAlgebraQuotient G K.2)
  exact ⟨Fintype.ofEquiv
    (CompletedGroupAlgebraQuotient G K.2 → R ⧸ I)
    (Finsupp.equivFunOnFinite.symm.trans
      (MonoidAlgebra.coeffEquiv
        (R := R ⧸ I) (M := CompletedGroupAlgebraQuotient G K.2)).symm)⟩

/-- Each open-finite quotient stage has its discrete topological-ring structure. -/
instance instIsTopologicalRingCompletedGroupAlgebraOpenFiniteQuotientSystemX
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    IsTopologicalRing
      ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) :=
  completedGroupAlgebraOpenFiniteQuotientStage_isTopologicalRing
    (R := R) (G := G) K

/-- The open-finite quotient limit inherits its topological-ring structure from the generic
ring-valued inverse limit. -/
instance instIsTopologicalRingCompletedGroupAlgebraOpenFiniteQuotientLimit :
    IsTopologicalRing (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) := by
  exact inferInstanceAs
    (IsTopologicalRing
      (completedGroupAlgebraOpenFiniteQuotientSystem R G).inverseLimit)

/-- The open-finite quotient limit is compact for compact topological coefficients. -/
theorem completedGroupAlgebraOpenFiniteQuotientLimit_compactSpace
    [IsTopologicalRing R] [CompactSpace R] :
    CompactSpace (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) := by
  let : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      CompactSpace ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := fun K => by
    let : Fintype ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) :=
      Classical.choice (completedGroupAlgebraOpenFiniteQuotientStage_fintype R G K)
    let : DiscreteTopology ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) :=
      completedGroupAlgebraOpenFiniteQuotientStage_discrete R G K
    infer_instance
  let : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      T2Space ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := fun K => by
    let : DiscreteTopology ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) :=
      completedGroupAlgebraOpenFiniteQuotientStage_discrete R G K
    infer_instance
  change CompactSpace
    (completedGroupAlgebraOpenFiniteQuotientSystem R G).inverseLimit
  infer_instance

/-- The open-finite quotient limit is Hausdorff. -/
theorem completedGroupAlgebraOpenFiniteQuotientLimit_t2Space :
    T2Space (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) := by
  let : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      T2Space ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := fun K => by
    let : DiscreteTopology ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) :=
      completedGroupAlgebraOpenFiniteQuotientStage_discrete R G K
    infer_instance
  exact (completedGroupAlgebraOpenFiniteQuotientSystem R G).t2Space_inverseLimit

/-- The open-finite quotient limit is totally disconnected. -/
theorem completedGroupAlgebraOpenFiniteQuotientLimit_totallyDisconnectedSpace :
    TotallyDisconnectedSpace (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) := by
  let : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      TotallyDisconnectedSpace ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := fun K =>
    by
      let : DiscreteTopology ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) :=
        completedGroupAlgebraOpenFiniteQuotientStage_discrete R G K
      infer_instance
  exact (completedGroupAlgebraOpenFiniteQuotientSystem R G).totallyDisconnectedSpace_inverseLimit

end

end CompletedGroupAlgebra
