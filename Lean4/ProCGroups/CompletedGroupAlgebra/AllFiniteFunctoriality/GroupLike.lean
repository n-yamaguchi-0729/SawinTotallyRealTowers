import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.Map

set_option autoImplicit false

/-!
# Completed Group Algebra / All Finite Functoriality / Group-Like

This module records the action of the all-finite functorial map on canonical group-like elements.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A group element maps to its image in the completed group algebra. -/
def completedGroupAlgebraOf (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (g : G) : CompletedGroupAlgebraCarrier R G :=
  toCompletedGroupAlgebra R G (MonoidAlgebra.of R G g)

/-- Projection of a completed group-like element to a finite quotient stage. -/
@[simp]
theorem completedGroupAlgebraProjection_of
    (U : CompletedGroupAlgebraIndex G) (g : G) :
    completedGroupAlgebraProjection R G U (completedGroupAlgebraOf R G g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) 1 := by
  rw [completedGroupAlgebraOf, completedGroupAlgebraProjection_toCompletedGroupAlgebra,
    completedGroupAlgebraStageMap_of]

/-- The completed group-like element attached to \(1\) is the unit. -/
@[simp]
theorem completedGroupAlgebraOf_one :
    completedGroupAlgebraOf R G 1 = (1 : CompletedGroupAlgebraCarrier R G) := by
  apply completedGroupAlgebra_ext (R := R) (G := G)
  intro U
  rw [completedGroupAlgebraProjection_of, map_one]
  change MonoidAlgebra.single
      (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U 1) (1 : R) = 1
  rfl

/-- Completed group-like elements multiply according to the group law. -/
@[simp]
theorem completedGroupAlgebraOf_mul (g h : G) :
    completedGroupAlgebraOf R G (g * h) =
      completedGroupAlgebraOf R G g * completedGroupAlgebraOf R G h := by
  change toCompletedGroupAlgebra R G (MonoidAlgebra.of R G (g * h)) =
    toCompletedGroupAlgebra R G (MonoidAlgebra.of R G g) *
      toCompletedGroupAlgebra R G (MonoidAlgebra.of R G h)
  rw [map_mul (MonoidAlgebra.of R G) g h]
  have happ (x : MonoidAlgebra R G) :
      toCompletedGroupAlgebraRingHom R G x = toCompletedGroupAlgebra R G x := rfl
  have hmul := map_mul (toCompletedGroupAlgebraRingHom R G)
    (MonoidAlgebra.of R G g) (MonoidAlgebra.of R G h)
  rw [happ, happ, happ] at hmul
  exact hmul

/-- The finite-stage group-like map \(G\to R[G/U]\) is continuous. -/
theorem continuous_completedGroupAlgebraStageMap_of
    (U : CompletedGroupAlgebraIndex G) :
    letI : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
      (completedGroupAlgebraSystem R G).topologicalSpace U
    Continuous fun g : G =>
      completedGroupAlgebraStageMap R G U (MonoidAlgebra.of R G g) := by
  let : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    (completedGroupAlgebraSystem R G).topologicalSpace U
  let : DiscreteTopology (CompletedGroupAlgebraQuotient G U) :=
    QuotientGroup.discreteTopology
      (ProCGroups.openNormalSubgroup_isOpen
        (G := G) ((OrderDual.ofDual U).1 : OpenNormalSubgroup G))
  have hbasis :
      @Continuous (CompletedGroupAlgebraQuotient G U)
        (CompletedGroupAlgebraStage R G U) inferInstance
        ((completedGroupAlgebraSystem R G).topologicalSpace U)
        (fun q => MonoidAlgebra.single q (1 : R)) :=
    continuous_of_discreteTopology
  have hproj :
      Continuous fun g : G =>
        openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g := by
    change Continuous
      (QuotientGroup.mk'
        (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G))
    exact continuous_quotient_mk'
  have hcont := hbasis.comp hproj
  change @Continuous G (CompletedGroupAlgebraStage R G U) (‹TopologicalSpace G›)
    ((completedGroupAlgebraSystem R G).topologicalSpace U)
    (fun g => MonoidAlgebra.single
      (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) (1 : R)) at hcont
  convert hcont using 1
  funext g
  exact completedGroupAlgebraStageMap_of (R := R) (G := G) U g

/-- The completed group-like map \(G \to \widehat{R[G]}\) is continuous. -/
theorem continuous_completedGroupAlgebraOf :
    Continuous (completedGroupAlgebraOf R G) := by
  let S := completedGroupAlgebraSystem R G
  let : ∀ U, TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    fun U => (completedGroupAlgebraSystem R G).topologicalSpace U
  let π : ∀ U : CompletedGroupAlgebraIndex G,
      G → CompletedGroupAlgebraStage R G U :=
    fun U g => completedGroupAlgebraStageMap R G U (MonoidAlgebra.of R G g)
  have hπ : ∀ U, Continuous (π U) := by
    intro U
    exact continuous_completedGroupAlgebraStageMap_of (R := R) (G := G) U
  have hcompat : S.CompatibleMaps π := by
    intro U V hUV
    funext g
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraStageMap_compatible
          (R := R) (G := G) hUV))
      (MonoidAlgebra.of R G g)
  change Continuous (S.inverseLimitLift π hcompat)
  exact S.continuous_inverseLimitLift π hπ hcompat

/--
The completed functorial map sends the group-like element attached to \(g\) to that of
\(\varphi(g)\).
-/
theorem completedGroupAlgebraMap_of
    (φ : G →* H) (hφ : Continuous φ) (g : G) :
    completedGroupAlgebraMap (G := G) (H := H) R φ hφ (completedGroupAlgebraOf R G g) =
      completedGroupAlgebraOf R H (φ g) := by
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraMap_comp_toCompletedGroupAlgebra (R := R) (G := G) (H := H)
        φ hφ))
      (MonoidAlgebra.of R G g)
  simpa [completedGroupAlgebraOf, toCompletedGroupAlgebraRingHom,
    finiteGroupAlgebra_mapDomainRingHom_of] using h

/-- The algebra-hom completed functorial map sends group-like elements to their images. -/
@[simp]
theorem completedGroupAlgebraMapAlgHom_of
    (φ : G →* H) (hφ : Continuous φ) (g : G) :
    completedGroupAlgebraMapAlgHom (G := G) (H := H) R φ hφ
        (completedGroupAlgebraOf R G g) =
      completedGroupAlgebraOf R H (φ g) :=
  completedGroupAlgebraMap_of (R := R) (G := G) (H := H) φ hφ g
end

end CompletedGroupAlgebra
