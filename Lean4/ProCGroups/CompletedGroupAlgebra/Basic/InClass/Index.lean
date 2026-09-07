import ProCGroups.CompletedGroupAlgebra.ProfiniteModules.FiniteGroupAlgebra.UnitRepresentation

set_option autoImplicit false

/-!
# Completed Group Algebra / Basic / Within a Class / Index

This module defines the reverse-ordered open normal subgroups whose quotients lie in a finite-group
class \(C\), together with their finite quotient groups and canonical quotient projections.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v w

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section InClass

/--
The \(C\)-indexed open-normal quotient tower for a completed group algebra. The order is chosen
so that larger indices give finer quotients.
-/
abbrev CompletedGroupAlgebraIndexInClass (C : ProCGroups.FiniteGroupClass.{v}) :=
  OrderDual (OpenNormalSubgroupInClass C G)

/-- The finite quotient \(G/U\) at one \(C\)-indexed stage. -/
abbrev CompletedGroupAlgebraQuotientInClass (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) : Type v :=
  (openNormalSubgroupInClassSystem C G).X U

/-- Quotients appearing in a finite quotient class are finite. -/
theorem finite_completedGroupAlgebraQuotientInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) :
    Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
  C.finite (OrderDual.ofDual U).2

/-- The terminal \(C\)-indexed completed-group-algebra quotient, corresponding to \(G/G\). -/
def terminalCompletedGroupAlgebraIndexInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    CompletedGroupAlgebraIndexInClass G C :=
  OrderDual.toDual (OpenNormalSubgroupInClass.top (C := C) (G := G))

omit [IsTopologicalGroup G] in
/-- The terminal in-class completed-group-algebra index is below every in-class index. -/
theorem terminalCompletedGroupAlgebraIndexInClass_le
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    terminalCompletedGroupAlgebraIndexInClass (G := G) C ≤ U := by
  change ((OrderDual.ofDual U).1 : Subgroup G) ≤ (⊤ : Subgroup G)
  exact le_top

variable (R : Type u) [CommRing R]

end InClass

end

end CompletedGroupAlgebra
