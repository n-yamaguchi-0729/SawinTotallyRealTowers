import ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Ring

set_option autoImplicit false

/-!
# Completed Group Algebra / Basic / All Finite / Projections

This module bundles the canonical all-finite stage projections and proves continuity of the
coefficient map through the inverse-limit lifting property.
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

/-- The coefficient-ring map \(R \to \widehat{R[G]}\) is continuous. -/
theorem continuous_completedGroupAlgebra_algebraMap :
    Continuous (algebraMap R (CompletedGroupAlgebraCarrier R G)) := by
  let S := completedGroupAlgebraSystem R G
  let : ∀ U, TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    fun U => (completedGroupAlgebraSystem R G).topologicalSpace U
  let π : ∀ U : CompletedGroupAlgebraIndex G,
      R → CompletedGroupAlgebraStage R G U :=
    fun U r => algebraMap R (CompletedGroupAlgebraStage R G U) r
  have hπ : ∀ U, Continuous (π U) := by
    intro U
    exact finiteGroupAlgebra_algebraMap_continuous R
      (CompletedGroupAlgebraQuotient G U)
  have hcompat : S.CompatibleMaps π := by
    intro U V hUV
    funext r
    exact completedGroupAlgebraTransition_algebraMap
      (R := R) (G := G) hUV r
  change Continuous (S.inverseLimitLift π hcompat)
  exact S.continuous_inverseLimitLift π hπ hcompat

/-- The canonical projection to a finite stage is bundled as an \(R\)-algebra homomorphism. -/
def completedGroupAlgebraProjectionAlgHom (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndex G) :
    CompletedGroupAlgebraCarrier R G →ₐ[R] CompletedGroupAlgebraStage R G U where
  toRingHom := completedGroupAlgebraProjection R G U
  commutes' := by
    intro r
    rfl

/-- The canonical projection to a finite stage, viewed as an \(R\)-linear map. -/
def completedGroupAlgebraProjectionLinearMap (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndex G) :
    CompletedGroupAlgebraCarrier R G →ₗ[R] CompletedGroupAlgebraStage R G U :=
  (completedGroupAlgebraProjectionAlgHom R G U).toLinearMap

/-- The finite-stage projection, as a continuous \(R\)-linear map. -/
def completedGroupAlgebraProjectionContinuousLinearMap (R : Type u) (G : Type v)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndex G) :
    letI : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
      (completedGroupAlgebraSystem R G).topologicalSpace U
    CompletedGroupAlgebraCarrier R G →L[R] CompletedGroupAlgebraStage R G U := by
  letI : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    (completedGroupAlgebraSystem R G).topologicalSpace U
  exact
    { toLinearMap := completedGroupAlgebraProjectionLinearMap R G U
      cont := (completedGroupAlgebraSystem R G).continuous_projection U }

end

end CompletedGroupAlgebra
