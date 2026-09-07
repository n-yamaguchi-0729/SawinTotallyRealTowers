import ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Carrier

set_option autoImplicit false

/-!
# Completed Group Algebra / Basic / All Finite / Ring Maps

The carrier and its algebraic structures come from the single generic inverse-limit construction.
This module adds the stagewise coefficient-change map and the coefficient algebra map. Generic
ring-homomorphism lemmas apply directly to the canonical bundled projections.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The all-finite completed-group-algebra coefficient-change map, obtained from the unique
inverse-limit lift of the stagewise coefficient maps. -/
def completedGroupAlgebraCoeffMap
    (S : Type w) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) :
    CompletedGroupAlgebraCarrier R G →+* CompletedGroupAlgebraCarrier S G where
  toFun x :=
    (completedGroupAlgebraCompatibleFamilyEquiv (R := S) (G := G)).symm
      ((completedGroupAlgebraSystem S G).inverseLimitLift
        (fun U x =>
          completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U
            (completedGroupAlgebraProjection R G U x))
        (by
          intro U V hUV
          funext x
          have hcompat := congrFun
            (congrArg DFunLike.coe
              (completedGroupAlgebraStageCoeffMap_compatible
                (R := R) (G := G) S f hUV))
            (completedGroupAlgebraProjection R G V x)
          calc
            completedGroupAlgebraTransition S G hUV
                (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f V
                  (completedGroupAlgebraProjection R G V x))
                =
              completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U
                (completedGroupAlgebraTransition R G hUV
                  (completedGroupAlgebraProjection R G V x)) := hcompat.symm
            _ =
              completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U
                (completedGroupAlgebraProjection R G U x) := by
                  rw [completedGroupAlgebraProjection_compatible]) x)
  map_zero' := by
    apply completedGroupAlgebra_ext (R := S) (G := G)
    intro U
    exact map_zero (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U)
  map_one' := by
    apply completedGroupAlgebra_ext (R := S) (G := G)
    intro U
    exact map_one (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U)
  map_add' x y := by
    apply completedGroupAlgebra_ext (R := S) (G := G)
    intro U
    exact map_add (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U)
      (completedGroupAlgebraProjection R G U x)
      (completedGroupAlgebraProjection R G U y)
  map_mul' x y := by
    apply completedGroupAlgebra_ext (R := S) (G := G)
    intro U
    exact map_mul (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U)
      (completedGroupAlgebraProjection R G U x)
      (completedGroupAlgebraProjection R G U y)

/-- Projection commutes with stagewise coefficient change. -/
@[simp]
theorem completedGroupAlgebraProjection_coeffMap
    (S : Type w) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) (U : CompletedGroupAlgebraIndex G)
    (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraProjection S G U
        (completedGroupAlgebraCoeffMap (R := R) (G := G) S f x) =
      completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U
        (completedGroupAlgebraProjection R G U x) :=
  rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Transition maps preserve scalar elements from the coefficient ring. -/
theorem completedGroupAlgebraTransition_algebraMap
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) (r : R) :
    completedGroupAlgebraTransition R G hUV
        (algebraMap R (CompletedGroupAlgebraStage R G V) r) =
      algebraMap R (CompletedGroupAlgebraStage R G U) r := by
  change
    MonoidAlgebra.mapDomain
        (OpenNormalSubgroupInClass.map hUV)
        (MonoidAlgebra.single 1 r) =
      MonoidAlgebra.single 1 r
  rw [MonoidAlgebra.mapDomain_single, map_one]

/-- The coefficient-ring map is the inverse-limit lift of the finite-stage algebra maps. -/
def completedGroupAlgebraAlgebraMap
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    R →+* CompletedGroupAlgebraCarrier R G where
  toFun r :=
    (completedGroupAlgebraCompatibleFamilyEquiv (R := R) (G := G)).symm
      ((completedGroupAlgebraSystem R G).inverseLimitLift
        (fun U r => algebraMap R (CompletedGroupAlgebraStage R G U) r)
        (by
          intro U V hUV
          funext r
          exact completedGroupAlgebraTransition_algebraMap
            (R := R) (G := G) hUV r) r)
  map_zero' := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    exact map_zero (algebraMap R (CompletedGroupAlgebraStage R G U))
  map_one' := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    exact map_one (algebraMap R (CompletedGroupAlgebraStage R G U))
  map_add' r s := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    exact map_add (algebraMap R (CompletedGroupAlgebraStage R G U)) r s
  map_mul' r s := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    exact map_mul (algebraMap R (CompletedGroupAlgebraStage R G U)) r s

/-- The completed group algebra is an algebra over its coefficient ring. -/
instance instAlgebraCompletedGroupAlgebra :
    Algebra R (CompletedGroupAlgebraCarrier R G) where
  algebraMap := completedGroupAlgebraAlgebraMap (R := R) (G := G)
  commutes' := by
    intro r x
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    exact Algebra.commutes r (completedGroupAlgebraProjection R G U x)
  smul_def' := by
    intro r x
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    change r • completedGroupAlgebraProjection R G U x =
      algebraMap R (CompletedGroupAlgebraStage R G U) r *
        completedGroupAlgebraProjection R G U x
    rw [Algebra.smul_def]

end

end CompletedGroupAlgebra
