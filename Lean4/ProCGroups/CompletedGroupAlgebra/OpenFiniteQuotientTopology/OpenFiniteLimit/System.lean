import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteQuotients

set_option autoImplicit false

/-!
# Completed Group Algebra / Open Finite Quotient Topology / Open Finite Limit / System

This module defines the two-parameter open-finite quotient system and its named inverse-limit
carrier. The compatible-family representation is exposed only by an explicit equivalence and the
canonical projection/compatibility/extensionality API.
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

/--
The two-parameter inverse system \(K = (I, U) \mapsto (R/I)[G/U]\) for the kernel-neighborhood
topology.
-/
def completedGroupAlgebraOpenFiniteQuotientSystem
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    ProCGroups.InverseSystems.InverseSystem
      (I := CompletedGroupAlgebraOpenQuotientIndex R G) where
  X := CompletedGroupAlgebraOpenQuotientStage R G
  topologicalSpace := completedGroupAlgebraOpenFiniteQuotientStageTopology R G
  map := fun {K L} hKL => completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
  continuous_map := by
    intro K L hKL
    let : TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
    let : TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G L) :=
      completedGroupAlgebraOpenFiniteQuotientStageTopology R G L
    have : DiscreteTopology (CompletedGroupAlgebraOpenQuotientStage R G L) :=
      completedGroupAlgebraOpenFiniteQuotientStage_discrete R G L
    exact continuous_of_discreteTopology
  map_id := by
    intro K
    exact congrArg DFunLike.coe
      (completedGroupAlgebraOpenFiniteQuotientTransition_id R G K)
  map_comp := by
    intro K L M hKL hLM
    exact congrArg DFunLike.coe
      (completedGroupAlgebraOpenFiniteQuotientTransition_comp R G hKL hLM)

/-- The two-parameter inverse limit \(\varprojlim_{I,U}(R/I)[G/U]\), kept opaque from
its concrete compatible-family realization. -/
def CompletedGroupAlgebraOpenFiniteQuotientLimit
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    Type (max u v) :=
  (completedGroupAlgebraOpenFiniteQuotientSystem R G).inverseLimit

/-- The two-parameter completion carries its inverse-limit topology. -/
instance instTopologicalSpaceCompletedGroupAlgebraOpenFiniteQuotientLimit :
    TopologicalSpace (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
  inferInstanceAs
    (TopologicalSpace
      (completedGroupAlgebraOpenFiniteQuotientSystem R G).inverseLimit)

/-- Explicit exchange between the named two-parameter carrier and its compatible-family model. -/
def completedGroupAlgebraOpenFiniteQuotientCompatibleFamilyEquiv :
    CompletedGroupAlgebraOpenFiniteQuotientLimit R G ≃
      (completedGroupAlgebraOpenFiniteQuotientSystem R G).inverseLimit :=
  Equiv.refl _

local instance (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    Ring ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := by
  change Ring (CompletedGroupAlgebraOpenQuotientStage R G K)
  infer_instance

/-- The open-finite quotient tower is a ring-valued inverse system. -/
instance instIsRingSystemCompletedGroupAlgebraOpenFiniteQuotientSystem :
    IsRingSystem (completedGroupAlgebraOpenFiniteQuotientSystem R G) where
  map_zero := by
    intro K L hKL
    exact map_zero (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL)
  map_one := by
    intro K L hKL
    exact map_one (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL)
  map_add := by
    intro K L hKL x y
    exact map_add (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL) x y
  map_mul := by
    intro K L hKL x y
    exact map_mul (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL) x y

/-- The two-parameter completion inherits its ring structure from the generic inverse limit. -/
instance instRingCompletedGroupAlgebraOpenFiniteQuotientLimit :
    Ring (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
  inferInstanceAs
    (Ring (completedGroupAlgebraOpenFiniteQuotientSystem R G).inverseLimit)

/-- The canonical projection to one quotient \((R/I)[G/U]\), bundled at its source as a ring
homomorphism. -/
def completedGroupAlgebraOpenFiniteQuotientLimitProjection
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    CompletedGroupAlgebraOpenFiniteQuotientLimit R G →+*
      CompletedGroupAlgebraOpenQuotientStage R G K := by
  change (completedGroupAlgebraOpenFiniteQuotientSystem R G).inverseLimit →+*
    (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K
  exact projectionRingHom
    (S := completedGroupAlgebraOpenFiniteQuotientSystem R G) K

/-- The open-finite quotient projections satisfy the two-parameter transition equations. -/
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjection_compatible
    {K L : CompletedGroupAlgebraOpenQuotientIndex R G} (hKL : K ≤ L)
    (x : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
    completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
        (completedGroupAlgebraOpenFiniteQuotientLimitProjection R G L x) =
      completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K x := by
  change (completedGroupAlgebraOpenFiniteQuotientSystem R G).map hKL
      ((completedGroupAlgebraOpenFiniteQuotientSystem R G).projection L x) =
    (completedGroupAlgebraOpenFiniteQuotientSystem R G).projection K x
  exact (completedGroupAlgebraOpenFiniteQuotientSystem R G).projection_compatible
    x K L hKL

/-- Two open-finite quotient completed elements are equal when all bundled coordinates agree. -/
@[ext]
theorem completedGroupAlgebraOpenFiniteQuotientLimit_ext
    {x y : CompletedGroupAlgebraOpenFiniteQuotientLimit R G}
    (h : ∀ K, completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K x =
      completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K y) :
    x = y := by
  apply (completedGroupAlgebraOpenFiniteQuotientSystem R G).ext
  intro K
  exact h K

end

end CompletedGroupAlgebra
