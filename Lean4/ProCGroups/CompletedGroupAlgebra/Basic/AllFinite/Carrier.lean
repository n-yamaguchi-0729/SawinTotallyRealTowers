import ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Stage

set_option autoImplicit false

/-!
# Completed Group Algebra / Basic / All Finite / Carrier

This module defines the all-finite completed group algebra as a named inverse-limit carrier.
Its compatible-family realization is available only through the explicit equivalence, coordinate
projection, compatibility, and extensionality API below. Ring and module structures are inherited
once from the generic inverse-limit construction.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The all-finite completed group algebra
\(\widehat{R[G]}=\varprojlim_U R[G/U]\), kept opaque from its compatible-family model. -/
def CompletedGroupAlgebraCarrier (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Type (max u v) :=
  (completedGroupAlgebraSystem R G).inverseLimit

/-- The completed group algebra carries the inverse-limit topology of its finite stages. -/
instance instTopologicalSpaceCompletedGroupAlgebraCarrier :
    TopologicalSpace (CompletedGroupAlgebraCarrier R G) :=
  inferInstanceAs (TopologicalSpace (completedGroupAlgebraSystem R G).inverseLimit)

/-- Explicit exchange between the named completed carrier and the concrete compatible-family
realization. Ordinary code should use finite-stage projections instead. -/
def completedGroupAlgebraCompatibleFamilyEquiv
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    CompletedGroupAlgebraCarrier R G ≃
      (completedGroupAlgebraSystem R G).inverseLimit :=
  Equiv.refl _

local instance instRingCompletedGroupAlgebraSystemStage
    (U : CompletedGroupAlgebraIndex G) :
    Ring ((completedGroupAlgebraSystem R G).X U) := by
  change Ring (CompletedGroupAlgebraStage R G U)
  infer_instance

local instance instModuleCompletedGroupAlgebraSystemStage
    (U : CompletedGroupAlgebraIndex G) :
    Module R ((completedGroupAlgebraSystem R G).X U) := by
  change Module R (CompletedGroupAlgebraStage R G U)
  infer_instance

/-- The all-finite tower is a ring-valued inverse system. -/
instance instIsRingSystemCompletedGroupAlgebraSystem :
    IsRingSystem (completedGroupAlgebraSystem R G) where
  map_zero := by
    intro U V hUV
    exact map_zero (completedGroupAlgebraTransition R G hUV)
  map_one := by
    intro U V hUV
    exact map_one (completedGroupAlgebraTransition R G hUV)
  map_add := by
    intro U V hUV x y
    exact map_add (completedGroupAlgebraTransition R G hUV) x y
  map_mul := by
    intro U V hUV x y
    exact map_mul (completedGroupAlgebraTransition R G hUV) x y

/-- The ring structure is inherited once from the generic ring inverse limit. -/
instance instRingCompletedGroupAlgebra :
    Ring (CompletedGroupAlgebraCarrier R G) := by
  change Ring (completedGroupAlgebraSystem R G).inverseLimit
  infer_instance

/-- The canonical finite-stage projection, bundled at its source as a ring homomorphism. -/
def completedGroupAlgebraProjection
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndex G) :
    CompletedGroupAlgebraCarrier R G →+* CompletedGroupAlgebraStage R G U := by
  change (completedGroupAlgebraSystem R G).inverseLimit →+*
    (completedGroupAlgebraSystem R G).X U
  exact projectionRingHom (S := completedGroupAlgebraSystem R G) U

/-- The canonical projections satisfy the inverse-system compatibility equations. -/
@[simp]
theorem completedGroupAlgebraProjection_compatible
    (x : CompletedGroupAlgebraCarrier R G)
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    completedGroupAlgebraTransition R G hUV
        (completedGroupAlgebraProjection R G V x) =
      completedGroupAlgebraProjection R G U x :=
  by
    change (completedGroupAlgebraSystem R G).map hUV
        ((completedGroupAlgebraSystem R G).projection V x) =
      (completedGroupAlgebraSystem R G).projection U x
    exact (completedGroupAlgebraSystem R G).projection_compatible x U V hUV

/-- Completed elements are equal when all bundled finite-stage projections agree. -/
@[ext]
theorem completedGroupAlgebra_ext {x y : CompletedGroupAlgebraCarrier R G}
    (h : ∀ U, completedGroupAlgebraProjection R G U x =
      completedGroupAlgebraProjection R G U y) :
    x = y := by
  apply (completedGroupAlgebraSystem R G).ext
  intro U
  exact h U

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Transition maps commute with coefficient scalar multiplication. -/
theorem completedGroupAlgebraTransition_smul
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V)
    (r : R) (x : CompletedGroupAlgebraStage R G V) :
    completedGroupAlgebraTransition R G hUV (r • x) =
      r • completedGroupAlgebraTransition R G hUV x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  change
    MonoidAlgebra.mapDomain
        (OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (MonoidAlgebra.single 1 r) =
      MonoidAlgebra.single 1 r
  rw [MonoidAlgebra.mapDomain_single, map_one]

/-- The all-finite tower is a module-valued inverse system over its coefficient ring. -/
instance instIsModuleSystemCompletedGroupAlgebra :
    @IsModuleSystem _ _ R _ (completedGroupAlgebraSystem R G)
      (fun U => @Ring.toAddCommGroup _
        (instRingCompletedGroupAlgebraSystemStage (G := G) (R := R) U))
      (fun U => instModuleCompletedGroupAlgebraSystemStage (G := G) (R := R) U) :=
  @IsModuleSystem.mk _ _ R _ (completedGroupAlgebraSystem R G)
    (fun U => @Ring.toAddCommGroup _
      (instRingCompletedGroupAlgebraSystemStage (G := G) (R := R) U))
    (fun U => instModuleCompletedGroupAlgebraSystemStage (G := G) (R := R) U)
    (completedGroupAlgebraTransition_smul (R := R) (G := G))

/-- The module structure is inherited once from the generic module inverse limit. -/
instance instModuleCoeffCompletedGroupAlgebra :
    Module R (CompletedGroupAlgebraCarrier R G) := by
  change Module R (completedGroupAlgebraSystem R G).inverseLimit
  exact @instModuleInverseLimitOfIsModuleSystem
    _ _ (completedGroupAlgebraSystem R G)
    (fun U => @Ring.toAddCommGroup _
      (instRingCompletedGroupAlgebraSystemStage (G := G) (R := R) U))
    (@isAddGroupSystemOfIsRingSystem _ _ (completedGroupAlgebraSystem R G)
      (fun U => instRingCompletedGroupAlgebraSystemStage (G := G) (R := R) U)
      (instIsRingSystemCompletedGroupAlgebraSystem G R))
    R inferInstance
    (fun U => instModuleCompletedGroupAlgebraSystemStage (G := G) (R := R) U)
    (@IsModuleSystem.mk _ _ R _ (completedGroupAlgebraSystem R G)
      (fun U => @Ring.toAddCommGroup _
        (instRingCompletedGroupAlgebraSystemStage (G := G) (R := R) U))
      (fun U => instModuleCompletedGroupAlgebraSystemStage (G := G) (R := R) U)
      (completedGroupAlgebraTransition_smul (R := R) (G := G)))

end

end CompletedGroupAlgebra
