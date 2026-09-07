import ProCGroups.CompletedGroupAlgebra.Basic.InClass.Index

set_option autoImplicit false

/-!
# Completed Group Algebra / Basic / All Finite / Index

This module defines the reverse-ordered finite-quotient indices for the all-finite completion,
their quotient groups and quotient projections, and the mutually inverse conversions with
\(C\)-indexed quotients when a formation contains all finite quotients of the group.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v w


variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The index set for the Section 5.3 completed group algebra tower, ordered so that larger indices
give finer finite quotients.
-/
abbrev CompletedGroupAlgebraIndex :=
  OrderDual (OpenNormalSubgroupInClass ProCGroups.FiniteGroupClass.allFinite G)

/-- The finite quotient \(G/U\) attached to one index of the completed-group-algebra tower. -/
abbrev CompletedGroupAlgebraQuotient (U : CompletedGroupAlgebraIndex G) : Type v :=
  (openNormalSubgroupInClassSystem ProCGroups.FiniteGroupClass.allFinite G).X U

/-- The finite completed group-algebra quotient is finite. -/
instance instFiniteCompletedGroupAlgebraQuotient
    (U : CompletedGroupAlgebraIndex G) :
    Finite (CompletedGroupAlgebraQuotient G U) :=
  (OrderDual.ofDual U).2

/-- The whole group \(G\), as a subgroup, used for the terminal quotient \(G/G\). -/
def terminalCompletedGroupAlgebraSubgroup : Subgroup G where
  carrier := Set.univ
  one_mem' := by simp only [Set.mem_univ]
  mul_mem' := by intro a b ha hb; simp only [Set.mem_univ]
  inv_mem' := by intro a ha; simp only [Set.mem_univ]

/-- The whole group \(G\) is an open subgroup. -/
def terminalCompletedGroupAlgebraOpenSubgroup : OpenSubgroup G :=
  OpenSubgroup.mk (terminalCompletedGroupAlgebraSubgroup G) isOpen_univ

/-- The whole group \(G\) is an open normal subgroup. -/
def terminalCompletedGroupAlgebraOpenNormalSubgroup : OpenNormalSubgroup G :=
  OpenNormalSubgroup.mk (terminalCompletedGroupAlgebraOpenSubgroup G)
    (Subgroup.Normal.mk (by
      intro n hn g
      simp only [terminalCompletedGroupAlgebraOpenSubgroup,
          terminalCompletedGroupAlgebraSubgroup, Subgroup.mem_mk,
  Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_univ]))

omit [IsTopologicalGroup G] in
/--
The terminal all-finite open normal subgroup has underlying subgroup equal to the top subgroup.
-/
@[simp]
theorem terminalCompletedGroupAlgebraOpenNormalSubgroup_coe :
    ((terminalCompletedGroupAlgebraOpenNormalSubgroup G : OpenNormalSubgroup G) : Subgroup G) =
      ⊤ := by
  ext g
  simp only [terminalCompletedGroupAlgebraOpenNormalSubgroup,
      terminalCompletedGroupAlgebraOpenSubgroup,
  terminalCompletedGroupAlgebraSubgroup, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_univ,
  Subgroup.mem_top]

/--
The terminal completed group-algebra quotient is a subsingleton, since it is the quotient by the
whole group.
-/
instance terminalCompletedGroupAlgebraQuotient_subsingleton :
    Subsingleton
      (G ⧸ ((terminalCompletedGroupAlgebraOpenNormalSubgroup G : OpenNormalSubgroup G) :
        Subgroup G)) := by
  rw [terminalCompletedGroupAlgebraOpenNormalSubgroup_coe (G := G)]
  constructor
  intro x y
  rcases QuotientGroup.mk'_surjective (⊤ : Subgroup G) x with ⟨a, rfl⟩
  rcases QuotientGroup.mk'_surjective (⊤ : Subgroup G) y with ⟨b, rfl⟩
  exact (QuotientGroup.eq).2 (by simp only [Subgroup.mem_top])

/-- The terminal open normal subgroup belongs to the finite-quotient indexing family. -/
def terminalCompletedGroupAlgebraSubgroupInClass :
    OpenNormalSubgroupInClass ProCGroups.FiniteGroupClass.allFinite G := by
  refine ⟨terminalCompletedGroupAlgebraOpenNormalSubgroup G, ?_⟩
  let : Subsingleton
      (G ⧸ ((terminalCompletedGroupAlgebraOpenNormalSubgroup G : OpenNormalSubgroup G) :
        Subgroup G)) :=
    terminalCompletedGroupAlgebraQuotient_subsingleton (G := G)
  exact Finite.of_subsingleton

/-- The terminal all-finite index, corresponding to the quotient \(G/G\). -/
def terminalCompletedGroupAlgebraIndex : CompletedGroupAlgebraIndex G :=
  OrderDual.toDual (terminalCompletedGroupAlgebraSubgroupInClass G)

/--
The completed group algebra is nonempty, with the terminal quotient or canonical base object as
witness.
-/
instance instNonemptyCompletedGroupAlgebraIndex :
    Nonempty (CompletedGroupAlgebraIndex G) :=
  ⟨terminalCompletedGroupAlgebraIndex G⟩

omit [IsTopologicalGroup G] in
/-- The terminal all-finite index is below every all-finite completed-group-algebra index. -/
theorem terminalCompletedGroupAlgebraIndex_le (U : CompletedGroupAlgebraIndex G) :
    terminalCompletedGroupAlgebraIndex G ≤ U := by
  change ((OrderDual.ofDual U).1 : Subgroup G) ≤
      ((terminalCompletedGroupAlgebraOpenNormalSubgroup G : OpenNormalSubgroup G) : Subgroup G)
  rw [terminalCompletedGroupAlgebraOpenNormalSubgroup_coe (G := G)]
  intro g hg
  simp only [Subgroup.mem_top]

/-- A quotient indexed by a finite quotient class is also an all-finite quotient. -/
def completedGroupAlgebraIndexInClassToAllFinite
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) : CompletedGroupAlgebraIndex G :=
  OrderDual.toDual
    ⟨(OrderDual.ofDual U).1, C.finite (OrderDual.ofDual U).property⟩

omit [IsTopologicalGroup G] in
/-- The comparison of all-finite and class-indexed indices is monotone. -/
theorem completedGroupAlgebraIndexInClassToAllFinite_le
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    completedGroupAlgebraIndexInClassToAllFinite G C U ≤
      completedGroupAlgebraIndexInClassToAllFinite G C V := by
  change ((OrderDual.ofDual V).1 : Subgroup G) ≤ ((OrderDual.ofDual U).1 : Subgroup G)
  exact hUV

/--
For a pro-\(C\) group over a formation, every all-finite open-normal quotient is a
\(C\)-quotient.
-/
def completedGroupAlgebraIndexToInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hG : HasOpenNormalBasisInClass C G)
    (U : CompletedGroupAlgebraIndex G) : CompletedGroupAlgebraIndexInClass G C :=
  OrderDual.toDual ⟨(OrderDual.ofDual U).1,
    HasOpenNormalBasisInClass.quotient_mem (C := C) hForm hG
      ((OrderDual.ofDual U).1 : OpenNormalSubgroup G)⟩

omit [IsTopologicalGroup G] in
/-- The comparison of all-finite and class-indexed indices is monotone. -/
theorem completedGroupAlgebraIndexToInClass_le
    (C : ProCGroups.FiniteGroupClass.{v}) (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hG : HasOpenNormalBasisInClass C G)
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    completedGroupAlgebraIndexToInClass G C hForm hG U ≤
      completedGroupAlgebraIndexToInClass G C hForm hG V := by
  change ((OrderDual.ofDual V).1 : Subgroup G) ≤ ((OrderDual.ofDual U).1 : Subgroup G)
  exact hUV

omit [IsTopologicalGroup G] in
/--
For a pro-\(C\) group, converting an all-finite completed-group-algebra index to the
\(C\)-indexed tower and then back to the all-finite tower returns the original index.
-/
@[simp]
theorem completedGroupAlgebraIndexInClassToAllFinite_indexToInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G)
    (U : CompletedGroupAlgebraIndex G) :
    completedGroupAlgebraIndexInClassToAllFinite G C
        (completedGroupAlgebraIndexToInClass G C hForm hG U) = U := by
  change (⟨(OrderDual.ofDual U).1,
      C.finite (HasOpenNormalBasisInClass.quotient_mem (C := C) hForm hG
        ((OrderDual.ofDual U).1 : OpenNormalSubgroup G))⟩ :
      OpenNormalSubgroupInClass ProCGroups.FiniteGroupClass.allFinite G) = OrderDual.ofDual U
  exact Subtype.ext rfl

omit [IsTopologicalGroup G] in
/--
For a pro-\(C\) group, converting a \(C\)-indexed completed-group-algebra index to the
all-finite tower and then back to the \(C\)-indexed tower returns the original index.
-/
@[simp]
theorem completedGroupAlgebraIndexToInClass_indexInClassToAllFinite
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G)
    (U : CompletedGroupAlgebraIndexInClass G C) :
    completedGroupAlgebraIndexToInClass G C hForm hG
        (completedGroupAlgebraIndexInClassToAllFinite G C U) = U := by
  change (⟨(OrderDual.ofDual U).1,
      HasOpenNormalBasisInClass.quotient_mem (C := C) hForm hG
        ((OrderDual.ofDual U).1 : OpenNormalSubgroup G)⟩ :
      OpenNormalSubgroupInClass C G) = OrderDual.ofDual U
  exact Subtype.ext rfl

end

end CompletedGroupAlgebra
