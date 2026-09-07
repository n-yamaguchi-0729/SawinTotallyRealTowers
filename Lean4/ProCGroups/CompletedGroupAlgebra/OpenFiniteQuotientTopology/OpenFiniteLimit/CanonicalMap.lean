import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteLimit.Topology

set_option autoImplicit false

/-!
# Completed Group Algebra / Open Finite Quotient Topology / Open Finite Limit / Canonical Map

This module lifts the compatible open-finite quotient maps from the abstract group algebra to the
named two-parameter completion, and proves its projection, continuity, and density properties.
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

/-- The abstract group-algebra map onto an open-finite quotient stage is surjective. -/
theorem groupAlgebraOpenFiniteQuotientMap_surjective
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    Function.Surjective (groupAlgebraOpenFiniteQuotientMap R G K) :=
  groupAlgebraFiniteQuotientMap_surjective (R := R) (G := G)
    ((OrderDual.ofDual K.1).1 : Ideal R) K.2

/-- The abstract group-algebra maps to open-finite quotient stages are compatible. -/
theorem groupAlgebraOpenFiniteQuotientMap_compatibleMaps
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    (completedGroupAlgebraOpenFiniteQuotientSystem R G).CompatibleMaps
      (fun K : CompletedGroupAlgebraOpenQuotientIndex R G =>
        groupAlgebraOpenFiniteQuotientMap R G K) := by
  intro K L hKL
  funext x
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraOpenFiniteQuotientTransition_comp_map R G hKL))
    x

/--
The two-parameter inverse limit \(\varprojlim_{I,U}(R/I)[G/U]\) appearing in Ribes--Zalesskii
Section 5.3.
-/
def toCompletedGroupAlgebraOpenFiniteQuotientLimit
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (x : MonoidAlgebra R G) :
    CompletedGroupAlgebraOpenFiniteQuotientLimit R G :=
  (completedGroupAlgebraOpenFiniteQuotientCompatibleFamilyEquiv
    (R := R) (G := G)).symm
    ((completedGroupAlgebraOpenFiniteQuotientSystem R G).inverseLimitLift
      (fun K => groupAlgebraOpenFiniteQuotientMap R G K)
      (groupAlgebraOpenFiniteQuotientMap_compatibleMaps R G) x)

/--
Projecting the canonical map to the open-finite quotient limit recovers the stage quotient map.
-/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjection_toLimit
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) (x : MonoidAlgebra R G) :
    completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K
        (toCompletedGroupAlgebraOpenFiniteQuotientLimit R G x) =
      groupAlgebraOpenFiniteQuotientMap R G K x :=
  rfl

/-- The canonical map from \(R[G]\) to the two-parameter limit is bundled as a ring homomorphism. -/
def toCompletedGroupAlgebraOpenFiniteQuotientLimitRingHom
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    MonoidAlgebra R G →+* CompletedGroupAlgebraOpenFiniteQuotientLimit R G where
  toFun := toCompletedGroupAlgebraOpenFiniteQuotientLimit R G
  map_zero' := by
    apply completedGroupAlgebraOpenFiniteQuotientLimit_ext (R := R) (G := G)
    intro K
    exact map_zero (groupAlgebraOpenFiniteQuotientMap R G K)
  map_one' := by
    apply completedGroupAlgebraOpenFiniteQuotientLimit_ext (R := R) (G := G)
    intro K
    exact map_one (groupAlgebraOpenFiniteQuotientMap R G K)
  map_add' x y := by
    apply completedGroupAlgebraOpenFiniteQuotientLimit_ext (R := R) (G := G)
    intro K
    exact map_add (groupAlgebraOpenFiniteQuotientMap R G K) x y
  map_mul' x y := by
    apply completedGroupAlgebraOpenFiniteQuotientLimit_ext (R := R) (G := G)
    intro K
    exact map_mul (groupAlgebraOpenFiniteQuotientMap R G K) x y

/--
The bundled ring homomorphism has the same underlying function as the coordinatewise
construction.
-/
@[simp]
theorem toCompletedGroupAlgebraOpenFiniteQuotientLimitRingHom_apply
    (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraOpenFiniteQuotientLimitRingHom R G x =
      toCompletedGroupAlgebraOpenFiniteQuotientLimit R G x :=
  rfl

/-- Projection after the canonical ring homomorphism is the corresponding open-finite quotient
map. -/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjection_comp_toLimit
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    (completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K).comp
        (toCompletedGroupAlgebraOpenFiniteQuotientLimitRingHom R G) =
      groupAlgebraOpenFiniteQuotientMap R G K := by
  apply RingHom.ext
  intro x
  rfl

/-- The canonical map to the open-finite quotient limit is continuous for the kernel topology. -/
theorem continuous_toCompletedGroupAlgebraOpenFiniteQuotientLimit_kernelTopology
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    Continuous (toCompletedGroupAlgebraOpenFiniteQuotientLimit R G) := by
  let : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  let S := completedGroupAlgebraOpenFiniteQuotientSystem R G
  let : ∀ K, TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    fun K => (completedGroupAlgebraOpenFiniteQuotientSystem R G).topologicalSpace K
  let π : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      MonoidAlgebra R G → CompletedGroupAlgebraOpenQuotientStage R G K :=
    fun K => groupAlgebraOpenFiniteQuotientMap R G K
  have hπ : ∀ K, Continuous (π K) := by
    intro K
    exact continuous_groupAlgebraOpenFiniteQuotientMap_kernelTopology R G K
  have hcompat : S.CompatibleMaps π :=
    groupAlgebraOpenFiniteQuotientMap_compatibleMaps R G
  change Continuous (S.inverseLimitLift π hcompat)
  exact S.continuous_inverseLimitLift π hπ hcompat

/--
The canonical map from `R[G]` has dense range in the two-parameter inverse limit
\(\varprojlim_{I,U}(R/I)[G/U]\).
-/
theorem denseRange_toCompletedGroupAlgebraOpenFiniteQuotientLimit
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    [Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    DenseRange (toCompletedGroupAlgebraOpenFiniteQuotientLimit R G) := by
  let S := completedGroupAlgebraOpenFiniteQuotientSystem R G
  let : TopologicalSpace (MonoidAlgebra R G) := ⊥
  have hdir :
      Directed (α := CompletedGroupAlgebraOpenQuotientIndex R G) (· ≤ ·) fun K => K :=
    directed_completedGroupAlgebraOpenQuotientIndex R G
  have hdense :
      DenseRange
        (S.inverseLimitLift
          (fun K : CompletedGroupAlgebraOpenQuotientIndex R G =>
            groupAlgebraOpenFiniteQuotientMap R G K)
          (groupAlgebraOpenFiniteQuotientMap_compatibleMaps R G)) :=
    S.denseRange_lift
      (fun K : CompletedGroupAlgebraOpenQuotientIndex R G =>
        groupAlgebraOpenFiniteQuotientMap R G K)
      (groupAlgebraOpenFiniteQuotientMap_compatibleMaps R G)
      (fun K => groupAlgebraOpenFiniteQuotientMap_surjective R G K)
      hdir
  change DenseRange
    (S.inverseLimitLift
      (fun K : CompletedGroupAlgebraOpenQuotientIndex R G =>
        groupAlgebraOpenFiniteQuotientMap R G K)
      (groupAlgebraOpenFiniteQuotientMap_compatibleMaps R G))
  exact hdense

end

end CompletedGroupAlgebra
