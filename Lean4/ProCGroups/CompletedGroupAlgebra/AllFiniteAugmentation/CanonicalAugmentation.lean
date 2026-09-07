import ProCGroups.CompletedGroupAlgebra.AllFiniteAugmentation.StageAugmentation

set_option autoImplicit false

/-!
# Completed Group Algebra / All Finite Augmentation / Canonical Augmentation

This module defines the all-finite canonical augmentation as the composition of a terminal
finite-stage augmentation with the canonical bundled projection, and proves that it can be
computed at every finite stage.
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

/-- The completed augmentation evaluated at a finite stage. -/
def completedGroupAlgebraAugmentationAt (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndex G) :
    CompletedGroupAlgebraCarrier R G → R :=
  fun x => completedGroupAlgebraStageAugmentation R G U (completedGroupAlgebraProjection R G U x)

/--
The coordinate defining the completed augmentation is independent of the chosen sufficiently
terminal index.
-/
@[simp]
theorem completedGroupAlgebraAugmentationAt_eq_of_le
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraAugmentationAt R G U x =
      completedGroupAlgebraAugmentationAt R G V x := by
  unfold completedGroupAlgebraAugmentationAt
  have hcomp := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraStageAugmentation_compatible (R := R) (G := G)
        (U := U) (V := V) hUV))
    (completedGroupAlgebraProjection R G V x)
  calc
    completedGroupAlgebraStageAugmentation R G U (completedGroupAlgebraProjection R G U x)
        =
      completedGroupAlgebraStageAugmentation R G U
        (completedGroupAlgebraTransition R G hUV (completedGroupAlgebraProjection R G V x)) := by
          rw [← completedGroupAlgebraProjection_compatible (R := R) (G := G) x hUV]
    _ = completedGroupAlgebraStageAugmentation R G V
        (completedGroupAlgebraProjection R G V x) := hcomp

/--
The canonical augmentation \(\varepsilon:\widehat{R[G]}\to R\) is the ring homomorphism obtained
by applying the finite-stage augmentation to any sufficiently terminal coordinate.
-/
def completedGroupAlgebraCanonicalAugmentation (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    CompletedGroupAlgebraCarrier R G →+* R :=
  (completedGroupAlgebraStageAugmentation R G
    (terminalCompletedGroupAlgebraIndex G)).comp
      (completedGroupAlgebraProjection R G
        (terminalCompletedGroupAlgebraIndex G))

/-- The canonical completed augmentation is computed at any finite stage. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_eq_at
    (U : CompletedGroupAlgebraIndex G) (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraCanonicalAugmentation R G x =
      completedGroupAlgebraAugmentationAt R G U x :=
  completedGroupAlgebraAugmentationAt_eq_of_le (R := R) (G := G)
    (U := terminalCompletedGroupAlgebraIndex G) (V := U)
    (terminalCompletedGroupAlgebraIndex_le (G := G) U) x

/--
For every finite quotient stage \(U\), projecting \(\widehat{R[G]}\) to \(R[G/U]\) and then
applying the finite-stage augmentation gives the canonical augmentation on \(\widehat{R[G]}\).
-/
@[simp]
theorem completedGroupAlgebraStageAugmentation_comp_projection
    (U : CompletedGroupAlgebraIndex G) :
    (completedGroupAlgebraStageAugmentation R G U).comp
        (completedGroupAlgebraProjection R G U) =
      completedGroupAlgebraCanonicalAugmentation R G := by
  apply RingHom.ext
  intro x
  exact (completedGroupAlgebraCanonicalAugmentation_eq_at (R := R) (G := G) U x).symm

/--
The canonical augmentation extends the abstract group-algebra augmentation through the dense
algebraic map.
-/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_toCompletedGroupAlgebra
    (x : MonoidAlgebra R G) :
    completedGroupAlgebraCanonicalAugmentation R G (toCompletedGroupAlgebra R G x) =
      groupAlgebraAugmentation R G x := by
  change completedGroupAlgebraStageAugmentation R G (terminalCompletedGroupAlgebraIndex G)
      (completedGroupAlgebraProjection R G (terminalCompletedGroupAlgebraIndex G)
        (toCompletedGroupAlgebra R G x)) = groupAlgebraAugmentation R G x
  rw [completedGroupAlgebraProjection_toCompletedGroupAlgebra]
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraStageAugmentation_comp_stageMap (R := R) (G := G)
        (terminalCompletedGroupAlgebraIndex G)))
    x

/-- Composing the canonical augmentation with the dense map gives the abstract augmentation. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_comp_toCompletedGroupAlgebra :
    (completedGroupAlgebraCanonicalAugmentation R G).comp
        (toCompletedGroupAlgebraRingHom R G) =
      groupAlgebraAugmentation R G := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraCanonicalAugmentation_toCompletedGroupAlgebra (R := R) (G := G) x

/-- Canonical augmentation is natural in the coefficient ring. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_comp_coeffMap
    (S : Type w) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) :
    (completedGroupAlgebraCanonicalAugmentation S G).comp
        (completedGroupAlgebraCoeffMap (R := R) (G := G) S f) =
      f.comp (completedGroupAlgebraCanonicalAugmentation R G) := by
  apply RingHom.ext
  intro x
  change
    completedGroupAlgebraStageAugmentation S G (terminalCompletedGroupAlgebraIndex G)
        (completedGroupAlgebraProjection S G (terminalCompletedGroupAlgebraIndex G)
          (completedGroupAlgebraCoeffMap (R := R) (G := G) S f x)) =
      f (completedGroupAlgebraStageAugmentation R G (terminalCompletedGroupAlgebraIndex G)
        (completedGroupAlgebraProjection R G (terminalCompletedGroupAlgebraIndex G) x))
  rw [completedGroupAlgebraProjection_coeffMap]
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraStageAugmentation_comp_stageCoeffMap
        (R := R) (G := G) S f (terminalCompletedGroupAlgebraIndex G)))
    (completedGroupAlgebraProjection R G (terminalCompletedGroupAlgebraIndex G) x)

/-- Canonical augmentation is natural with respect to functorial completed group-algebra maps. -/
@[simp 900]
theorem completedGroupAlgebraCanonicalAugmentation_map
    (φ : G →* H) (hφ : Continuous φ)
    (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraCanonicalAugmentation R H
        (completedGroupAlgebraMap (G := G) (H := H) R φ hφ x) =
      completedGroupAlgebraCanonicalAugmentation R G x := by
  let V : CompletedGroupAlgebraIndex H := terminalCompletedGroupAlgebraIndex H
  calc
    completedGroupAlgebraCanonicalAugmentation R H
        (completedGroupAlgebraMap (G := G) (H := H) R φ hφ x)
        =
      completedGroupAlgebraAugmentationAt R H V
        (completedGroupAlgebraMap (G := G) (H := H) R φ hφ x) := by
          exact completedGroupAlgebraCanonicalAugmentation_eq_at (R := R) (G := H) V
            (completedGroupAlgebraMap (G := G) (H := H) R φ hφ x)
    _ =
      completedGroupAlgebraStageAugmentation R H V
        (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) φ hφ V
          (completedGroupAlgebraProjection R G
            (completedGroupAlgebraComapIndex (G := G) φ hφ V) x)) := by
          rw [completedGroupAlgebraAugmentationAt, completedGroupAlgebraProjection_map]
    _ =
      completedGroupAlgebraStageAugmentation R G
        (completedGroupAlgebraComapIndex (G := G) φ hφ V)
        (completedGroupAlgebraProjection R G
          (completedGroupAlgebraComapIndex (G := G) φ hφ V) x) := by
          have hstage := congrFun
            (congrArg DFunLike.coe
              (completedGroupAlgebraStageAugmentation_comp_functorialStageMap
                (R := R) (G := G) (H := H) φ hφ V))
            (completedGroupAlgebraProjection R G
              (completedGroupAlgebraComapIndex (G := G) φ hφ V) x)
          exact hstage
    _ =
      completedGroupAlgebraCanonicalAugmentation R G x := by
          exact (completedGroupAlgebraCanonicalAugmentation_eq_at (R := R) (G := G)
            (completedGroupAlgebraComapIndex (G := G) φ hφ V) x).symm

/-- Canonical augmentation after the functorial completed map agrees with canonical augmentation. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_comp_map
    (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraCanonicalAugmentation R H).comp
        (completedGroupAlgebraMap (G := G) (H := H) R φ hφ) =
      completedGroupAlgebraCanonicalAugmentation R G := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraCanonicalAugmentation_map (R := R) (G := G) (H := H) φ hφ x

/-- The canonical augmentation sends every completed group-like element to one. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_of (g : G) :
    completedGroupAlgebraCanonicalAugmentation R G (completedGroupAlgebraOf R G g) = 1 := by
  rw [completedGroupAlgebraOf,
    completedGroupAlgebraCanonicalAugmentation_toCompletedGroupAlgebra]
  simp only [MonoidAlgebra.of_apply, groupAlgebraAugmentation_single]

/-- The canonical augmentation \(\varepsilon:\widehat{R[G]}\to R\) is surjective. -/
theorem completedGroupAlgebraCanonicalAugmentation_surjective :
    Function.Surjective (completedGroupAlgebraCanonicalAugmentation R G) := by
  intro r
  refine ⟨toCompletedGroupAlgebra R G (algebraMap R (MonoidAlgebra R G) r), ?_⟩
  rw [completedGroupAlgebraCanonicalAugmentation_toCompletedGroupAlgebra]
  simp only [MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id,
      Function.comp_apply, id_eq,
  groupAlgebraAugmentation_single]

/--
The canonical augmentation \(\varepsilon:\widehat{R[G]}\to R\) is continuous for the
inverse-limit topology on \(\widehat{R[G]}\).
-/
theorem continuous_completedGroupAlgebraCanonicalAugmentation :
    Continuous (completedGroupAlgebraCanonicalAugmentation R G) := by
  let U := terminalCompletedGroupAlgebraIndex G
  let : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    (completedGroupAlgebraSystem R G).topologicalSpace U
  change Continuous fun x : CompletedGroupAlgebraCarrier R G =>
    completedGroupAlgebraStageAugmentation R G U (completedGroupAlgebraProjection R G U x)
  exact (finiteGroupAlgebra_augmentation_continuous R (CompletedGroupAlgebraQuotient G U)).comp
    ((completedGroupAlgebraSystem R G).continuous_projection U)

end

end CompletedGroupAlgebra
