import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.Comap
import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.CanonicalMaps

set_option autoImplicit false

/-!
# Completed Group Algebra / All Finite Functoriality / Stage Map

This module lifts the quotient homomorphism from `Comap` to finite group algebras and proves its
continuity, transition compatibility, and compatibility with the canonical dense stage maps.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v w

variable (R : Type u) [CommRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The finite-stage map \(R[G/\varphi^{-1}(V)]\to R[H/V]\) is induced by the continuous
homomorphism \(\varphi : G \to H\).
-/
def completedGroupAlgebraFunctorialStageMap
    (R : Type u) [CommRing R]
    (φ : G →* H) (hφ : Continuous φ) (V : CompletedGroupAlgebraIndex H) :
    CompletedGroupAlgebraStage R G (completedGroupAlgebraComapIndex (G := G) φ hφ V) →+*
      CompletedGroupAlgebraStage R H V :=
  MonoidAlgebra.mapDomainRingHom R
    (completedGroupAlgebraComapQuotientMap (G := G) φ hφ V)

/-- A surjective group homomorphism induces a surjective finite-stage algebra map. -/
theorem completedGroupAlgebraFunctorialStageMap_surjective_of_surjective
    (φ : G →* H) (hφ : Continuous φ)
    (hφsurj : Function.Surjective φ) (V : CompletedGroupAlgebraIndex H) :
    Function.Surjective
      (completedGroupAlgebraFunctorialStageMap
        (G := G) (H := H) (R := R) φ hφ V) := by
  intro x
  obtain ⟨y, hy⟩ :=
    Finsupp.mapDomain_surjective (M := R)
      (completedGroupAlgebraComapQuotientMap_surjective
        (G := G) φ hφ hφsurj V) x.coeff
  refine ⟨MonoidAlgebra.ofCoeff y, ?_⟩
  apply MonoidAlgebra.coeff_injective
  exact hy

/--
The finite-stage functorial map induced by \(\varphi : G \to H\) carries a singleton basis
function on \(G/\varphi^{-1}(V)\) to the singleton basis function on \(H/V\) supported at the
induced image, with unchanged coefficient.
-/
@[simp]
theorem completedGroupAlgebraFunctorialStageMap_single
    (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H)
    (q : CompletedGroupAlgebraQuotient G
      (completedGroupAlgebraComapIndex (G := G) φ hφ V)) (r : R) :
    completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) φ hφ V
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single (completedGroupAlgebraComapQuotientMap (G := G) φ hφ V q) r := by
  change
    MonoidAlgebra.mapDomain
        (completedGroupAlgebraComapQuotientMap (G := G) φ hφ V)
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        (completedGroupAlgebraComapQuotientMap (G := G) φ hφ V q) r
  exact MonoidAlgebra.mapDomain_single

/-- The finite-stage functorial map preserves scalar algebra-map elements. -/
theorem completedGroupAlgebraFunctorialStageMap_algebraMap
    (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) (r : R) :
    completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) φ hφ V
        (algebraMap R
          (CompletedGroupAlgebraStage R G
            (completedGroupAlgebraComapIndex (G := G) φ hφ V)) r) =
      algebraMap R (CompletedGroupAlgebraStage R H V) r := by
  change
    MonoidAlgebra.mapDomain
        (completedGroupAlgebraComapQuotientMap (G := G) φ hφ V)
        (MonoidAlgebra.single 1 r) =
      MonoidAlgebra.single 1 r
  rw [MonoidAlgebra.mapDomain_single,
    (completedGroupAlgebraComapQuotientMap (G := G) φ hφ V).map_one]

/-- The finite-stage functorial map is continuous for the finite-stage topologies. -/
theorem continuous_completedGroupAlgebraFunctorialStageMap
    [TopologicalSpace R] [IsTopologicalRing R]
    (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) :
    letI : TopologicalSpace
        (CompletedGroupAlgebraStage R G (completedGroupAlgebraComapIndex (G := G) φ hφ V)) :=
      (completedGroupAlgebraSystem R G).topologicalSpace
        (completedGroupAlgebraComapIndex (G := G) φ hφ V)
    letI : TopologicalSpace (CompletedGroupAlgebraStage R H V) :=
      (completedGroupAlgebraSystem R H).topologicalSpace V
    Continuous (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R)
      φ hφ V) := by
  let : TopologicalSpace
      (CompletedGroupAlgebraStage R G (completedGroupAlgebraComapIndex (G := G) φ hφ V)) :=
    (completedGroupAlgebraSystem R G).topologicalSpace
      (completedGroupAlgebraComapIndex (G := G) φ hφ V)
  let : TopologicalSpace (CompletedGroupAlgebraStage R H V) :=
    (completedGroupAlgebraSystem R H).topologicalSpace V
  exact finiteGroupAlgebra_mapDomainRingHom_continuous R
    (CompletedGroupAlgebraQuotient G (completedGroupAlgebraComapIndex (G := G) φ hφ V))
    (CompletedGroupAlgebraQuotient H V)
    (completedGroupAlgebraComapQuotientMap (G := G) φ hφ V)

/--
Functorial finite-stage maps commute with the transition maps attached to refinements of finite
quotients.
-/
@[simp]
theorem completedGroupAlgebraFunctorialStageMap_transition
    (φ : G →* H) (hφ : Continuous φ)
    {V W : CompletedGroupAlgebraIndex H} (hVW : V ≤ W) :
    (completedGroupAlgebraTransition R H hVW).comp
        (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) φ hφ W) =
      (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) φ hφ V).comp
        (completedGroupAlgebraTransition R G
          (completedGroupAlgebraComapIndex_mono (G := G) φ hφ hVW)) := by
  have hVW' :
      (((OrderDual.ofDual W).1 : OpenNormalSubgroup H) : Subgroup H) ≤
        (((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H) :=
    hVW
  have hcomap :
      (((OrderDual.ofDual (completedGroupAlgebraComapIndex (G := G) φ hφ W)).1 :
        OpenNormalSubgroup G) : Subgroup G) ≤
        (((OrderDual.ofDual (completedGroupAlgebraComapIndex (G := G) φ hφ V)).1 :
          OpenNormalSubgroup G) : Subgroup G) :=
    completedGroupAlgebraComapIndex_mono (G := G) φ hφ hVW
  have hmaps :
      (OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := H)
        (U := OrderDual.ofDual V) (V := OrderDual.ofDual W) hVW').comp
          (completedGroupAlgebraComapQuotientMap (G := G) φ hφ W) =
        (completedGroupAlgebraComapQuotientMap (G := G) φ hφ V).comp
          (OpenNormalSubgroupInClass.map
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
            (U := OrderDual.ofDual
              (completedGroupAlgebraComapIndex (G := G) φ hφ V))
            (V := OrderDual.ofDual
              (completedGroupAlgebraComapIndex (G := G) φ hφ W)) hcomap) := by
    apply MonoidHom.ext
    intro q
    rcases QuotientGroup.mk'_surjective
        ((((OrderDual.ofDual (completedGroupAlgebraComapIndex (G := G) φ hφ W)).1 :
          OpenNormalSubgroup G) : Subgroup G)) q with
      ⟨g, rfl⟩
    rfl
  unfold completedGroupAlgebraTransition completedGroupAlgebraFunctorialStageMap
  exact
    (MonoidAlgebra.mapDomainRingHom_comp (R := R)
      (OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := H)
        (U := OrderDual.ofDual V) (V := OrderDual.ofDual W) hVW')
      (completedGroupAlgebraComapQuotientMap (G := G) φ hφ W)).symm.trans
      ((congrArg (MonoidAlgebra.mapDomainRingHom R) hmaps).trans
        (MonoidAlgebra.mapDomainRingHom_comp (R := R)
          (completedGroupAlgebraComapQuotientMap (G := G) φ hφ V)
          (OpenNormalSubgroupInClass.map
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
            (U := OrderDual.ofDual
              (completedGroupAlgebraComapIndex (G := G) φ hφ V))
            (V := OrderDual.ofDual
              (completedGroupAlgebraComapIndex (G := G) φ hφ W)) hcomap)))

/-- The finite-stage functorial map agrees with the dense stage map after applying \(\varphi\). -/
@[simp]
theorem completedGroupAlgebraFunctorialStageMap_comp_stageMap
    (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) :
    (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) φ hφ V).comp
        (completedGroupAlgebraStageMap R G
          (completedGroupAlgebraComapIndex (G := G) φ hφ V)) =
      (completedGroupAlgebraStageMap R H V).comp
        (MonoidAlgebra.mapDomainRingHom R φ) := by
  have hmaps :
      (completedGroupAlgebraComapQuotientMap (G := G) φ hφ V).comp
          (openNormalSubgroupInClassProj
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
            (completedGroupAlgebraComapIndex (G := G) φ hφ V)) =
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := H) V).comp φ := by
    apply MonoidHom.ext
    intro g
    exact completedGroupAlgebraComapQuotientMap_mk (G := G) φ hφ V g
  unfold completedGroupAlgebraFunctorialStageMap completedGroupAlgebraStageMap
  exact
    (MonoidAlgebra.mapDomainRingHom_comp (R := R)
      (completedGroupAlgebraComapQuotientMap (G := G) φ hφ V)
      (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
        (completedGroupAlgebraComapIndex (G := G) φ hφ V))).symm.trans
      ((congrArg (MonoidAlgebra.mapDomainRingHom R) hmaps).trans
        (MonoidAlgebra.mapDomainRingHom_comp (R := R)
          (openNormalSubgroupInClassProj
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := H) V) φ))

end

end CompletedGroupAlgebra
