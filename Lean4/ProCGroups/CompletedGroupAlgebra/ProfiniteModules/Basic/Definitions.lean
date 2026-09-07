import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Category.Profinite.Basic
import ProCGroups.InverseSystems.FiniteStageFactorization

set_option autoImplicit false

/-!
# Bundled profinite rings and modules

This file defines profinite rings, commutative profinite coefficient rings, and profinite modules.
It also states their free-extension, discreteness, and finite-index submodule-basis properties.
-/

open scoped Topology

namespace CompletedGroupAlgebra

universe u v w z

/-- A profinite ring object.  Its standard algebraic and topological structures are stored once on
the carrier. -/
structure ProfiniteRing where
  /-- The underlying profinite space. -/
  toProfinite : Profinite.{u}
  /-- The ring structure on the underlying profinite space. -/
  [ring : Ring toProfinite]
  /-- The assertion that the ring operations are continuous. -/
  [isTopologicalRing : IsTopologicalRing toProfinite]

attribute [instance] ProfiniteRing.ring ProfiniteRing.isTopologicalRing

namespace ProfiniteRing

/-- A bundled profinite ring coerces to its underlying profinite type. -/
instance : CoeSort ProfiniteRing.{u} (Type u) where
  coe Λ := Λ.toProfinite

end ProfiniteRing

/-- A commutative profinite ring, used as the coefficient object for completed group algebras.
The completed algebra itself may be noncommutative and therefore uses `ProfiniteRing`.  This
separate bundle avoids installing a second `Ring` instance on `ProfiniteRing`. -/
structure ProfiniteCommRing where
  /-- The underlying profinite space. -/
  toProfinite : Profinite.{u}
  /-- The commutative ring structure on the underlying profinite space. -/
  [commRing : CommRing toProfinite]
  /-- The assertion that the ring operations are continuous. -/
  [isTopologicalRing : IsTopologicalRing toProfinite]

attribute [instance] ProfiniteCommRing.commRing ProfiniteCommRing.isTopologicalRing

namespace ProfiniteCommRing

/-- A bundled profinite commutative ring coerces to its underlying profinite type. -/
instance : CoeSort ProfiniteCommRing.{u} (Type u) where
  coe R := R.toProfinite

/-- Forget commutativity while retaining the bundled profinite ring object. -/
def toProfiniteRing (R : ProfiniteCommRing.{u}) : ProfiniteRing.{u} where
  toProfinite := R.toProfinite
  ring := inferInstance
  isTopologicalRing := inferInstance

end ProfiniteCommRing

/-- A topological module over a topological ring. -/
def IsTopologicalModuleOver (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ]
    [AddCommGroup M] [TopologicalSpace M] [Module Λ M] : Prop :=
  IsTopologicalRing Λ ∧ IsTopologicalAddGroup M ∧ ContinuousSMul Λ M

/-- A profinite module object over a fixed profinite ring. -/
structure ProfiniteModule (Λ : ProfiniteRing.{u}) where
  /-- The underlying profinite space. -/
  toProfinite : Profinite.{v}
  /-- The additive commutative group structure on the underlying profinite space. -/
  [addCommGroup : AddCommGroup toProfinite]
  /-- The \(\Lambda\)-module structure on the underlying profinite space. -/
  [module : Module Λ toProfinite]
  /-- The assertion that addition and negation are continuous. -/
  [isTopologicalAddGroup : IsTopologicalAddGroup toProfinite]
  /-- The assertion that scalar multiplication by \(\Lambda\) is jointly continuous. -/
  [continuousSMul : ContinuousSMul Λ toProfinite]

attribute [instance] ProfiniteModule.addCommGroup
attribute [instance] ProfiniteModule.module
attribute [instance] ProfiniteModule.isTopologicalAddGroup
attribute [instance] ProfiniteModule.continuousSMul

namespace ProfiniteModule

/-- A bundled profinite module coerces to its underlying profinite type. -/
instance (Λ : ProfiniteRing.{u}) : CoeSort (ProfiniteModule.{u, v} Λ) (Type v) where
  coe M := M.toProfinite

/-- The extension-and-uniqueness property from a candidate free profinite module to one bundled
target.  Keeping the target as an argument makes this API universe-polymorphic without `ULift`. -/
def HasFreeLiftTo {Λ : ProfiniteRing.{u}} (M : ProfiniteModule.{u, w} Λ)
    (X : Type v) [TopologicalSpace X] (ι : X → M)
    (N : ProfiniteModule.{u, z} Λ) : Prop :=
  ∀ f : X → N, Continuous f →
    ∃! F : M →L[Λ] N, ∀ x : X, F (ι x) = f x

/-- Universal-property predicate for a free profinite module in a fixed ambient universe.
Cross-universe targets use `HasFreeLiftTo` directly.  The scalar, generator, and source/target
modules are bundled objects, so their profiniteness is part of the statement. -/
def IsFreeOn {Λ : ProfiniteRing.{u}} (M : ProfiniteModule.{u, w} Λ)
    (X : Profinite.{v}) (ι : X → M) : Prop :=
  Continuous ι ∧
    closure (Submodule.span Λ (Set.range ι) : Set M) = Set.univ ∧
      ∀ N : ProfiniteModule.{u, w} Λ, HasFreeLiftTo M X ι N

end ProfiniteModule

/-- A topological module whose underlying module topology is discrete. -/
def IsDiscreteModule (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace Λ]
    [AddCommGroup M] [TopologicalSpace M] [Module Λ M] : Prop :=
  IsTopologicalModuleOver Λ M ∧ DiscreteTopology M

/-- Finite-index submodules form a neighborhood basis at zero. -/
def HasFiniteIndexSubmoduleBasis (Λ : Type u) (M : Type v) [Ring Λ] [TopologicalSpace M]
    [AddCommGroup M] [Module Λ M] : Prop :=
  ∀ U ∈ 𝓝 (0 : M), ∃ N : Submodule Λ M,
    IsOpen (N : Set M) ∧ (N : Set M) ⊆ U ∧ Nonempty (Fintype (M ⧸ N))

end CompletedGroupAlgebra
