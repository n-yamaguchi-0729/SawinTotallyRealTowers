import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.StageMap

set_option autoImplicit false

/-!
# Completed Group Algebra / All Finite Functoriality / Map

This module lifts the functorial finite-stage maps to the named all-finite completed carrier and
proves their algebraic, topological, and dense-subalgebra characterizations.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
In Lemma 5.3.5(e), map construction, a continuous homomorphism of profinite groups \(\varphi : G
\to H\) induces a continuous ring homomorphism \(\widehat{R[G]} \to \widehat{R[H]}\).
-/
def completedGroupAlgebraMap
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (φ : G →* H) (hφ : Continuous φ) :
    CompletedGroupAlgebraCarrier R G →+* CompletedGroupAlgebraCarrier R H where
  toFun x :=
    (completedGroupAlgebraCompatibleFamilyEquiv (R := R) (G := H)).symm
      ((completedGroupAlgebraSystem R H).inverseLimitLift
        (fun V x =>
          completedGroupAlgebraFunctorialStageMap
            (G := G) (H := H) (R := R) φ hφ V
            (completedGroupAlgebraProjection R G
              (completedGroupAlgebraComapIndex (G := G) φ hφ V) x))
        (by
          intro V W hVW
          funext x
          have hcomp := congrFun
            (congrArg DFunLike.coe
              (completedGroupAlgebraFunctorialStageMap_transition
                (R := R) (G := G) (H := H) φ hφ hVW))
              (completedGroupAlgebraProjection R G
              (completedGroupAlgebraComapIndex (G := G) φ hφ W) x)
          rw [RingHom.comp_apply, RingHom.comp_apply] at hcomp
          simp only
          rw [← completedGroupAlgebraProjection_compatible
            (R := R) (G := G) x
            (completedGroupAlgebraComapIndex_mono
              (G := G) φ hφ hVW)]
          exact hcomp) x)
  map_zero' := by
    apply completedGroupAlgebra_ext (R := R) (G := H)
    intro V
    exact map_zero (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R)
      φ hφ V)
  map_one' := by
    apply completedGroupAlgebra_ext (R := R) (G := H)
    intro V
    exact map_one (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R)
      φ hφ V)
  map_add' x y := by
    apply completedGroupAlgebra_ext (R := R) (G := H)
    intro V
    exact map_add (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R)
      φ hφ V)
      (completedGroupAlgebraProjection R G
        (completedGroupAlgebraComapIndex (G := G) φ hφ V) x)
      (completedGroupAlgebraProjection R G
        (completedGroupAlgebraComapIndex (G := G) φ hφ V) y)
  map_mul' x y := by
    apply completedGroupAlgebra_ext (R := R) (G := H)
    intro V
    exact map_mul (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R)
      φ hφ V)
      (completedGroupAlgebraProjection R G
        (completedGroupAlgebraComapIndex (G := G) φ hφ V) x)
      (completedGroupAlgebraProjection R G
        (completedGroupAlgebraComapIndex (G := G) φ hφ V) y)

/-- Projection of the completed functorial map is computed by the corresponding stage map. -/
@[simp]
theorem completedGroupAlgebraProjection_map
    (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraProjection R H V
        (completedGroupAlgebraMap (G := G) (H := H) R φ hφ x) =
      completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) φ hφ V
        (completedGroupAlgebraProjection R G
          (completedGroupAlgebraComapIndex (G := G) φ hφ V) x) :=
  rfl

/--
In Lemma 5.3.5(e), algebra form, a continuous homomorphism of profinite groups induces an
\(R\)-algebra homomorphism on completed group algebras.
-/
def completedGroupAlgebraMapAlgHom
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (φ : G →* H) (hφ : Continuous φ) :
    CompletedGroupAlgebraCarrier R G →ₐ[R] CompletedGroupAlgebraCarrier R H where
  toRingHom := completedGroupAlgebraMap (G := G) (H := H) R φ hφ
  commutes' := by
    intro r
    apply completedGroupAlgebra_ext (R := R) (G := H)
    intro V
    change completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) φ hφ V
        (algebraMap R
          (CompletedGroupAlgebraStage R G
            (completedGroupAlgebraComapIndex (G := G) φ hφ V)) r) =
      algebraMap R (CompletedGroupAlgebraStage R H V) r
    exact completedGroupAlgebraFunctorialStageMap_algebraMap
      (R := R) (G := G) (H := H) φ hφ V r

/--
The algebra homomorphism form of the completed functorial map has the same underlying function
as the corresponding completed ring homomorphism.
-/
@[simp]
theorem completedGroupAlgebraMapAlgHom_apply
    (φ : G →* H) (hφ : Continuous φ)
    (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraMapAlgHom (G := G) (H := H) R φ hφ x =
      completedGroupAlgebraMap (G := G) (H := H) R φ hφ x :=
  rfl

/-- The completed group-algebra map induced by a continuous group homomorphism is continuous. -/
theorem continuous_completedGroupAlgebraMap
    (φ : G →* H) (hφ : Continuous φ) :
    Continuous (completedGroupAlgebraMap (G := G) (H := H) R φ hφ) := by
  let S := completedGroupAlgebraSystem R H
  let : ∀ V, TopologicalSpace (CompletedGroupAlgebraStage R H V) :=
    fun V => (completedGroupAlgebraSystem R H).topologicalSpace V
  let π : ∀ V : CompletedGroupAlgebraIndex H,
      CompletedGroupAlgebraCarrier R G → CompletedGroupAlgebraStage R H V :=
    fun V x =>
      completedGroupAlgebraFunctorialStageMap
        (G := G) (H := H) (R := R) φ hφ V
        (completedGroupAlgebraProjection R G
          (completedGroupAlgebraComapIndex (G := G) φ hφ V) x)
  have hπ : ∀ V, Continuous (π V) := by
    intro V
    let : TopologicalSpace
        (CompletedGroupAlgebraStage R G (completedGroupAlgebraComapIndex (G := G) φ hφ V)) :=
      (completedGroupAlgebraSystem R G).topologicalSpace
        (completedGroupAlgebraComapIndex (G := G) φ hφ V)
    exact (continuous_completedGroupAlgebraFunctorialStageMap (R := R) (G := G) (H := H)
      φ hφ V).comp
        ((completedGroupAlgebraSystem R G).continuous_projection
          (completedGroupAlgebraComapIndex (G := G) φ hφ V))
  have hcompat : S.CompatibleMaps π := by
    intro V W hVW
    funext x
    have hcomp := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraFunctorialStageMap_transition
          (R := R) (G := G) (H := H) φ hφ hVW))
      (completedGroupAlgebraProjection R G
        (completedGroupAlgebraComapIndex (G := G) φ hφ W) x)
    rw [RingHom.comp_apply, RingHom.comp_apply] at hcomp
    simp only [S, π]
    rw [← completedGroupAlgebraProjection_compatible
      (R := R) (G := G) x
      (completedGroupAlgebraComapIndex_mono (G := G) φ hφ hVW)]
    exact hcomp
  change Continuous (S.inverseLimitLift π hcompat)
  exact S.continuous_inverseLimitLift π hπ hcompat

/--
The completed functorial map agrees on the dense abstract group algebra with the ordinary
group-algebra map induced by the group homomorphism.
-/
theorem completedGroupAlgebraMap_comp_toCompletedGroupAlgebra
    (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraMap (G := G) (H := H) R φ hφ).comp
        (toCompletedGroupAlgebraRingHom R G) =
      (toCompletedGroupAlgebraRingHom R H).comp (MonoidAlgebra.mapDomainRingHom R φ) := by
  apply RingHom.ext
  intro x
  apply completedGroupAlgebra_ext (R := R) (G := H)
  intro V
  have hstage := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraFunctorialStageMap_comp_stageMap (R := R) (G := G) (H := H)
        φ hφ V))
    x
  change completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) φ hφ V
      (completedGroupAlgebraStageMap R G
        (completedGroupAlgebraComapIndex (G := G) φ hφ V) x) =
    completedGroupAlgebraStageMap R H V (MonoidAlgebra.mapDomainRingHom R φ x)
  exact hstage

end

end CompletedGroupAlgebra
