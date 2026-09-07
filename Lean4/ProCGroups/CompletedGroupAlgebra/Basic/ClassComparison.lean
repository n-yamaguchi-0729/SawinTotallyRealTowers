import ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Topology
import ProCGroups.CompletedGroupAlgebra.Basic.InClass.Topology

set_option autoImplicit false

/-!
# Completed Group Algebra / Basic / Class Comparison

This module compares the all-finite and \(C\)-indexed named completed carriers through their
canonical projections, and bundles the resulting inverse maps as ring, algebra, and topological
equivalences for pro-\(C\) groups.
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

/-- The projection from the all-finite completion to a stage indexed by a finite quotient class
\(C\), bundled as a ring homomorphism. -/
def completedGroupAlgebraProjectionToStageInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraCarrier R G →+* CompletedGroupAlgebraStageInClass C R G U :=
  completedGroupAlgebraProjection R G
    (completedGroupAlgebraIndexInClassToAllFinite G C U)

/--
The all-finite projection to a \(C\)-indexed stage is compatible with the transition maps of the
\(C\)-indexed tower.
-/
theorem completedGroupAlgebraProjectionToStageInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraTransitionInClass C R G hUV
        (completedGroupAlgebraProjectionToStageInClass (R := R) (G := G) C V x) =
      completedGroupAlgebraProjectionToStageInClass (R := R) (G := G) C U x := by
  change completedGroupAlgebraTransition R G
      (completedGroupAlgebraIndexInClassToAllFinite_le (G := G) C hUV)
      (completedGroupAlgebraProjection R G
        (completedGroupAlgebraIndexInClassToAllFinite G C V) x) =
    completedGroupAlgebraProjection R G
      (completedGroupAlgebraIndexInClassToAllFinite G C U) x
  exact completedGroupAlgebraProjection_compatible (R := R) (G := G) x
    (completedGroupAlgebraIndexInClassToAllFinite_le (G := G) C hUV)

/--
The comparison map from the ordinary all-finite completed group algebra to the inverse limit
over any finite-quotient class.
-/
def completedGroupAlgebraToInClass
    (C : ProCGroups.FiniteGroupClass.{v}) :
    CompletedGroupAlgebraCarrier R G → CompletedGroupAlgebraInClass C R G :=
  fun x =>
    (completedGroupAlgebraInClassCompatibleFamilyEquiv
      (R := R) (G := G) C).symm
      ((completedGroupAlgebraSystemInClass C R G).inverseLimitLift
        (fun U =>
          completedGroupAlgebraProjectionToStageInClass
            (R := R) (G := G) C U)
        (by
          intro U V hUV
          funext x
          exact completedGroupAlgebraProjectionToStageInClass_compatible
            (R := R) (G := G) C hUV x) x)

/--
Projecting the comparison map \(\widehat{R[G]}\to\widehat{R[G]}_{C}\) to a \(C\)-indexed finite
stage recovers the corresponding all-finite projection.
-/
@[simp]
theorem completedGroupAlgebraToInClass_projection
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraProjectionInClass C R G U
        (completedGroupAlgebraToInClass (R := R) (G := G) C x) =
      completedGroupAlgebraProjectionToStageInClass (R := R) (G := G) C U x :=
  rfl

/--
The comparison from the all-finite completed group algebra to the \(C\)-indexed inverse limit is
bundled as a ring homomorphism.
-/
def completedGroupAlgebraToInClassRingHom
    (C : ProCGroups.FiniteGroupClass.{v}) :
    CompletedGroupAlgebraCarrier R G →+* CompletedGroupAlgebraInClass C R G where
  toFun := completedGroupAlgebraToInClass (R := R) (G := G) C
  map_zero' := by
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    rfl
  map_one' := by
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    rfl
  map_add' x y := by
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    rfl
  map_mul' x y := by
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    rfl

/--
The comparison map from the all-finite completed group algebra to the \(C\)-indexed model is
evaluated by reading the corresponding finite-stage coordinate.
-/
@[simp]
theorem completedGroupAlgebraToInClassRingHom_apply
    (C : ProCGroups.FiniteGroupClass.{v})
    (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraToInClassRingHom (R := R) (G := G) C x =
      completedGroupAlgebraToInClass (R := R) (G := G) C x :=
  rfl

/--
The comparison from the all-finite completed group algebra to the \(C\)-indexed inverse limit,
as an \(R\)-algebra homomorphism.
-/
def completedGroupAlgebraToInClassAlgHom
    (C : ProCGroups.FiniteGroupClass.{v}) :
    CompletedGroupAlgebraCarrier R G →ₐ[R] CompletedGroupAlgebraInClass C R G where
  toRingHom := completedGroupAlgebraToInClassRingHom (R := R) (G := G) C
  commutes' := by
    intro r
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    rfl

/--
The comparison map from the all-finite completed group algebra to the \(C\)-indexed model is
evaluated by reading the corresponding finite-stage coordinate.
-/
@[simp]
theorem completedGroupAlgebraToInClassAlgHom_apply
    (C : ProCGroups.FiniteGroupClass.{v})
    (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraToInClassAlgHom (R := R) (G := G) C x =
      completedGroupAlgebraToInClass (R := R) (G := G) C x :=
  rfl

/--
The comparison map from the all-finite completed group algebra to the \(C\)-indexed completed
group algebra is continuous for the inverse-limit topology.
-/
theorem continuous_completedGroupAlgebraToInClass
    (C : ProCGroups.FiniteGroupClass.{v}) :
    Continuous (completedGroupAlgebraToInClass (R := R) (G := G) C ) := by
  let S := completedGroupAlgebraSystemInClass C R G
  let : ∀ U, TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    fun U => (completedGroupAlgebraSystemInClass C R G).topologicalSpace U
  let π : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      CompletedGroupAlgebraCarrier R G →
        CompletedGroupAlgebraStageInClass C R G U :=
    fun U => completedGroupAlgebraProjectionToStageInClass
      (R := R) (G := G) C U
  have hπ : ∀ U, Continuous (π U) := by
    intro U
    change Continuous ((completedGroupAlgebraSystem R G).projection
      (completedGroupAlgebraIndexInClassToAllFinite G C U))
    exact (completedGroupAlgebraSystem R G).continuous_projection
      (completedGroupAlgebraIndexInClassToAllFinite G C U)
  have hcompat : S.CompatibleMaps π := by
    intro U V hUV
    funext x
    exact completedGroupAlgebraProjectionToStageInClass_compatible
      (R := R) (G := G) C hUV x
  change Continuous (S.inverseLimitLift π hcompat)
  exact S.continuous_inverseLimitLift π hπ hcompat

/--
For a pro-\(C\) group, the \(C\)-indexed inverse limit maps back to the ordinary all-finite
completed group algebra by reading the same open-normal quotient stages.
-/
def completedGroupAlgebraFromInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    CompletedGroupAlgebraInClass C R G → CompletedGroupAlgebraCarrier R G :=
  fun x =>
    (completedGroupAlgebraCompatibleFamilyEquiv (R := R) (G := G)).symm
      ((completedGroupAlgebraSystem R G).inverseLimitLift
        (fun U : CompletedGroupAlgebraIndex G =>
          completedGroupAlgebraProjectionInClass C R G
            (completedGroupAlgebraIndexToInClass G C hForm hG U))
        (by
          intro U V hUV
          funext x
          change completedGroupAlgebraTransitionInClass C R G
              (completedGroupAlgebraIndexToInClass_le
                (G := G) C hForm hG hUV)
              (completedGroupAlgebraProjectionInClass C R G
                (completedGroupAlgebraIndexToInClass G C hForm hG V) x) =
            completedGroupAlgebraProjectionInClass C R G
              (completedGroupAlgebraIndexToInClass G C hForm hG U) x
          exact completedGroupAlgebraProjectionInClass_compatible
            (R := R) (G := G) C
            (completedGroupAlgebraIndexToInClass_le
              (G := G) C hForm hG hUV) x) x)

/--
Projecting the comparison map \(\widehat{R[G]}_{C}\to\widehat{R[G]}\) to an all-finite stage
recovers the matching \(C\)-indexed projection.
-/
@[simp]
theorem completedGroupAlgebraFromInClass_projection
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) (U :
        CompletedGroupAlgebraIndex G)
    (x : CompletedGroupAlgebraInClass C R G) :
    completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x) =
      completedGroupAlgebraProjectionInClass C R G
        (completedGroupAlgebraIndexToInClass G C hForm hG U) x :=
  rfl

/--
The ring-homomorphism form of the comparison map is the bundled ring map determined by the
underlying coordinate formula for the completed group algebra.
-/
def completedGroupAlgebraFromInClassRingHom
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    CompletedGroupAlgebraInClass C R G →+* CompletedGroupAlgebraCarrier R G where
  toFun := completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG
  map_zero' := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    change completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG 0) =
      completedGroupAlgebraProjection R G U (0 : CompletedGroupAlgebraCarrier R G)
    rw [completedGroupAlgebraFromInClass_projection]
    exact map_zero (completedGroupAlgebraProjectionInClass C R G
      (completedGroupAlgebraIndexToInClass G C hForm hG U))
  map_one' := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    change completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG 1) =
      completedGroupAlgebraProjection R G U (1 : CompletedGroupAlgebraCarrier R G)
    rw [completedGroupAlgebraFromInClass_projection]
    exact map_one (completedGroupAlgebraProjectionInClass C R G
      (completedGroupAlgebraIndexToInClass G C hForm hG U))
  map_add' x y := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    change completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG (x + y)) =
      completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x +
          completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG y)
    rw [completedGroupAlgebraFromInClass_projection]
    exact map_add (completedGroupAlgebraProjectionInClass C R G
      (completedGroupAlgebraIndexToInClass G C hForm hG U)) x y
  map_mul' x y := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    change completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG (x * y)) =
      completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x *
          completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG y)
    rw [completedGroupAlgebraFromInClass_projection]
    exact map_mul (completedGroupAlgebraProjectionInClass C R G
      (completedGroupAlgebraIndexToInClass G C hForm hG U)) x y

/--
The comparison map from the \(C\)-indexed completed group algebra to the all-finite model is
evaluated by reading the corresponding finite-stage coordinate.
-/
@[simp]
theorem completedGroupAlgebraFromInClassRingHom_apply
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) (x :
        CompletedGroupAlgebraInClass C R G) :
    completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG x =
      completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x :=
  rfl

/--
The algebra homomorphism form of the comparison map is the bundled algebra map determined by the
underlying coordinate formula for the completed group algebra.
-/
def completedGroupAlgebraFromInClassAlgHom
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    CompletedGroupAlgebraInClass C R G →ₐ[R] CompletedGroupAlgebraCarrier R G where
  toRingHom := completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG
  commutes' := by
    intro r
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    change completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG
          (algebraMap R (CompletedGroupAlgebraInClass C R G) r)) =
      completedGroupAlgebraProjection R G U (algebraMap R (CompletedGroupAlgebraCarrier R G) r)
    rw [completedGroupAlgebraFromInClass_projection]
    change completedGroupAlgebraProjectionInClass C R G
        (completedGroupAlgebraIndexToInClass G C hForm hG U)
        (algebraMap R (CompletedGroupAlgebraInClass C R G) r) =
      algebraMap R (CompletedGroupAlgebraStage R G U) r
    exact completedGroupAlgebraProjectionInClass_algebraMap (R := R) (G := G) C
      (completedGroupAlgebraIndexToInClass G C hForm hG U) r

/--
The comparison map from the \(C\)-indexed completed group algebra to the all-finite model is
evaluated by reading the corresponding finite-stage coordinate.
-/
@[simp]
theorem completedGroupAlgebraFromInClassAlgHom_apply
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) (x :
        CompletedGroupAlgebraInClass C R G) :
    completedGroupAlgebraFromInClassAlgHom (R := R) (G := G) C hForm hG x =
      completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x :=
  rfl

/--
The comparison map from the \(C\)-indexed completed group algebra to the all-finite completed
group algebra is continuous for the inverse-limit topology.
-/
theorem continuous_completedGroupAlgebraFromInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    Continuous (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG) := by
  let S := completedGroupAlgebraSystem R G
  let : ∀ U, TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    fun U => (completedGroupAlgebraSystem R G).topologicalSpace U
  let π : ∀ U : CompletedGroupAlgebraIndex G,
      CompletedGroupAlgebraInClass C R G →
        CompletedGroupAlgebraStage R G U :=
    fun U => completedGroupAlgebraProjectionInClass C R G
      (completedGroupAlgebraIndexToInClass G C hForm hG U)
  have hπ : ∀ U, Continuous (π U) := by
    intro U
    let : TopologicalSpace
        (CompletedGroupAlgebraStageInClass C R G (completedGroupAlgebraIndexToInClass G C hForm
            hG U)) :=
      (completedGroupAlgebraSystemInClass C R G).topologicalSpace
        (completedGroupAlgebraIndexToInClass G C hForm hG U)
    change Continuous (completedGroupAlgebraProjectionInClass C R G
      (completedGroupAlgebraIndexToInClass G C hForm hG U))
    simpa using continuous_completedGroupAlgebraProjectionInClass
      (R := R) (G := G) C (completedGroupAlgebraIndexToInClass G C hForm hG U)
  have hcompat : S.CompatibleMaps π := by
    intro U V hUV
    funext x
    change completedGroupAlgebraTransitionInClass C R G
        (completedGroupAlgebraIndexToInClass_le
          (G := G) C hForm hG hUV)
        (completedGroupAlgebraProjectionInClass C R G
          (completedGroupAlgebraIndexToInClass G C hForm hG V) x) =
      completedGroupAlgebraProjectionInClass C R G
        (completedGroupAlgebraIndexToInClass G C hForm hG U) x
    exact completedGroupAlgebraProjectionInClass_compatible
      (R := R) (G := G) C
      (completedGroupAlgebraIndexToInClass_le
        (G := G) C hForm hG hUV) x
  change Continuous (S.inverseLimitLift π hcompat)
  exact S.continuous_inverseLimitLift π hπ hcompat

/--
The composite from a \(C\)-indexed completion to the all-finite completion and back is the
identity on the \(C\)-indexed completion.
-/
@[simp]
theorem completedGroupAlgebraFromInClass_toInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) (x :
        CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG
        (completedGroupAlgebraToInClass (R := R) (G := G) C x) = x := by
  apply completedGroupAlgebra_ext (R := R) (G := G)
  intro U
  rw [completedGroupAlgebraFromInClass_projection, completedGroupAlgebraToInClass_projection]
  change completedGroupAlgebraProjection R G
      (completedGroupAlgebraIndexInClassToAllFinite G C
        (completedGroupAlgebraIndexToInClass G C hForm hG U)) x =
    completedGroupAlgebraProjection R G U x
  cases U
  rfl

/--
The composite from the all-finite completion to the \(C\)-indexed completion and back is the
identity on the all-finite completion.
-/
@[simp]
theorem completedGroupAlgebraToInClass_fromInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) (x :
        CompletedGroupAlgebraInClass C R G) :
    completedGroupAlgebraToInClass (R := R) (G := G) C
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x) = x := by
  apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
  intro U
  rw [completedGroupAlgebraToInClass_projection]
  change completedGroupAlgebraProjection R G
      (completedGroupAlgebraIndexInClassToAllFinite G C U)
      (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x) =
    completedGroupAlgebraProjectionInClass C R G U x
  rw [completedGroupAlgebraFromInClass_projection]
  change completedGroupAlgebraProjectionInClass C R G
      (completedGroupAlgebraIndexToInClass G C hForm hG
        (completedGroupAlgebraIndexInClassToAllFinite G C U)) x =
    completedGroupAlgebraProjectionInClass C R G U x
  cases U
  rfl

/-- The two comparison ring homomorphisms are inverse to one another after composition. -/
@[simp]
theorem completedGroupAlgebraFromInClassRingHom_comp_toInClassRingHom
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG).comp
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C ) =
      RingHom.id (CompletedGroupAlgebraCarrier R G) := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraFromInClass_toInClass (R := R) (G := G) C hForm hG x

/-- The two comparison ring homomorphisms are inverse to one another after composition. -/
@[simp]
theorem completedGroupAlgebraToInClassRingHom_comp_fromInClassRingHom
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C ).comp
        (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG) =
      RingHom.id (CompletedGroupAlgebraInClass C R G) := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraToInClass_fromInClass (R := R) (G := G) C hForm hG x

/--
For a pro-\(C\) group, the all-finite and \(C\)-indexed completed group algebras are the same
ring, via the comparison maps.
-/
def completedGroupAlgebraInClassRingEquiv
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    CompletedGroupAlgebraCarrier R G ≃+* CompletedGroupAlgebraInClass C R G where
  toFun := completedGroupAlgebraToInClass (R := R) (G := G) C
  invFun := completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG
  left_inv := by
    intro x
    exact completedGroupAlgebraFromInClass_toInClass (R := R) (G := G) C hForm hG x
  right_inv := by
    intro x
    exact completedGroupAlgebraToInClass_fromInClass (R := R) (G := G) C hForm hG x
  map_mul' := by
    intro x y
    exact map_mul (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C ) x y
  map_add' := by
    intro x y
    exact map_add (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C ) x y

/--
The comparison equivalence is evaluated by the underlying all-finite or \(C\)-indexed comparison
map.
-/
@[simp]
theorem completedGroupAlgebraInClassRingEquiv_apply
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) (x :
        CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraInClassRingEquiv (R := R) (G := G) C hForm hG x =
      completedGroupAlgebraToInClass (R := R) (G := G) C x :=
  rfl

/--
The comparison equivalence is evaluated by the underlying all-finite or \(C\)-indexed comparison
map.
-/
@[simp]
theorem completedGroupAlgebraInClassRingEquiv_symm_apply
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) (x :
        CompletedGroupAlgebraInClass C R G) :
    (completedGroupAlgebraInClassRingEquiv (R := R) (G := G) C hForm hG).symm x =
      completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x :=
  rfl

/--
For a pro-\(C\) group, the all-finite and \(C\)-indexed completed group algebras are the same
\(R\)-algebra.
-/
def completedGroupAlgebraInClassAlgEquiv
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    CompletedGroupAlgebraCarrier R G ≃ₐ[R] CompletedGroupAlgebraInClass C R G :=
  AlgEquiv.ofRingEquiv (f := completedGroupAlgebraInClassRingEquiv (R := R) (G := G) C hForm hG)
    (by
      intro r
      rfl)

/--
The comparison equivalence is evaluated by the underlying all-finite or \(C\)-indexed comparison
map.
-/
@[simp]
theorem completedGroupAlgebraInClassAlgEquiv_apply
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) (x :
        CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraInClassAlgEquiv (R := R) (G := G) C hForm hG x =
      completedGroupAlgebraToInClass (R := R) (G := G) C x :=
  rfl

/--
The comparison equivalence is evaluated by the underlying all-finite or \(C\)-indexed comparison
map.
-/
@[simp]
theorem completedGroupAlgebraInClassAlgEquiv_symm_apply
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) (x :
        CompletedGroupAlgebraInClass C R G) :
    (completedGroupAlgebraInClassAlgEquiv (R := R) (G := G) C hForm hG).symm x =
      completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x :=
  rfl

/-- The comparison equivalence is an equivalence of topological spaces. -/
def completedGroupAlgebraInClassHomeomorph
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    CompletedGroupAlgebraCarrier R G ≃ₜ CompletedGroupAlgebraInClass C R G where
  toEquiv := (completedGroupAlgebraInClassRingEquiv (R := R) (G := G) C hForm hG).toEquiv
  continuous_toFun := continuous_completedGroupAlgebraToInClass (R := R) (G := G) C
  continuous_invFun := continuous_completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG

/--
The comparison homeomorphism is evaluated by the underlying all-finite or \(C\)-indexed
comparison map.
-/
@[simp]
theorem completedGroupAlgebraInClassHomeomorph_apply
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) (x :
        CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraInClassHomeomorph (R := R) (G := G) C hForm hG x =
      completedGroupAlgebraToInClass (R := R) (G := G) C x :=
  rfl

/--
The comparison homeomorphism is evaluated by the underlying all-finite or \(C\)-indexed
comparison map.
-/
@[simp]
theorem completedGroupAlgebraInClassHomeomorph_symm_apply
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) (x :
        CompletedGroupAlgebraInClass C R G) :
    (completedGroupAlgebraInClassHomeomorph (R := R) (G := G) C hForm hG).symm x =
      completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x :=
  rfl

/--
Surjectivity of the induced map is obtained from surjectivity on the underlying quotient or
dense algebraic model, together with closedness of the image in the completed target.
-/
theorem completedGroupAlgebraToInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    Function.Surjective (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C ) := by
  intro x
  refine ⟨completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG x, ?_⟩
  exact completedGroupAlgebraToInClass_fromInClass (R := R) (G := G) C hForm hG x

/--
Surjectivity of the induced map is obtained from surjectivity on the underlying quotient or
dense algebraic model, together with closedness of the image in the completed target.
-/
theorem completedGroupAlgebraFromInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    Function.Surjective (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG) := by
  intro x
  refine ⟨completedGroupAlgebraToInClass (R := R) (G := G) C x, ?_⟩
  exact completedGroupAlgebraFromInClass_toInClass (R := R) (G := G) C hForm hG x

end

end CompletedGroupAlgebra
