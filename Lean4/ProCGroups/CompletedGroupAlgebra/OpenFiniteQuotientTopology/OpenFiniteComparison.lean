import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteLimit.CanonicalMap
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Topology.Homeomorph.TransferInstance

set_option autoImplicit false

/-!
# Completed Group Algebra / Open Finite Quotient Topology / Open Finite Comparison

This module compares the named fixed-coefficient completion with the named two-parameter
open-finite quotient completion and studies the induced topology, injectivity, density, and
coefficient-quotient kernels.
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

/--
The canonical map from the fixed-coefficient completed group algebra \(\widehat{R[G]}\) to the
two-parameter limit \(\varprojlim_{I,U} (R/I)[G/U]\).
-/
def completedGroupAlgebraToOpenFiniteQuotientLimit
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (x : CompletedGroupAlgebraCarrier R G) :
    CompletedGroupAlgebraOpenFiniteQuotientLimit R G :=
  (completedGroupAlgebraOpenFiniteQuotientCompatibleFamilyEquiv
    (R := R) (G := G)).symm
    ((completedGroupAlgebraOpenFiniteQuotientSystem R G).inverseLimitLift
      (fun K => completedGroupAlgebraOpenFiniteQuotientProjection R G K)
      (by
        intro K L hKL
        funext x
        exact congrFun
          (congrArg DFunLike.coe
            (completedGroupAlgebraOpenFiniteQuotientTransition_comp_projection
              R G hKL))
          x) x)

/--
The open-finite-limit projection after the comparison from the completed group algebra is the
original finite-stage projection.
-/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjection_fromCompleted
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K
        (completedGroupAlgebraToOpenFiniteQuotientLimit R G x) =
      completedGroupAlgebraOpenFiniteQuotientProjection R G K x :=
  rfl

/--
The comparison from the completed group algebra to the open-finite quotient limit agrees with
the canonical dense map on abstract group-algebra elements.
-/
@[simp]
theorem completedGroupAlgebraToOpenFiniteQuotientLimit_toCompletedGroupAlgebra
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (x : MonoidAlgebra R G) :
    completedGroupAlgebraToOpenFiniteQuotientLimit R G (toCompletedGroupAlgebra R G x) =
      toCompletedGroupAlgebraOpenFiniteQuotientLimit R G x := by
  apply completedGroupAlgebraOpenFiniteQuotientLimit_ext (R := R) (G := G)
  intro K
  rfl

/--
The canonical map \(\widehat{R[G]} \to \varprojlim_{I,U} (R/I)[G/U]\) is bundled as a ring
homomorphism.
-/
def completedGroupAlgebraToOpenFiniteQuotientLimitRingHom
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    CompletedGroupAlgebraCarrier R G →+* CompletedGroupAlgebraOpenFiniteQuotientLimit R G where
  toFun := completedGroupAlgebraToOpenFiniteQuotientLimit R G
  map_zero' := by
    apply completedGroupAlgebraOpenFiniteQuotientLimit_ext (R := R) (G := G)
    intro K
    exact map_zero (completedGroupAlgebraOpenFiniteQuotientProjection R G K)
  map_one' := by
    apply completedGroupAlgebraOpenFiniteQuotientLimit_ext (R := R) (G := G)
    intro K
    exact map_one (completedGroupAlgebraOpenFiniteQuotientProjection R G K)
  map_add' x y := by
    apply completedGroupAlgebraOpenFiniteQuotientLimit_ext (R := R) (G := G)
    intro K
    exact map_add (completedGroupAlgebraOpenFiniteQuotientProjection R G K) x y
  map_mul' x y := by
    apply completedGroupAlgebraOpenFiniteQuotientLimit_ext (R := R) (G := G)
    intro K
    exact map_mul (completedGroupAlgebraOpenFiniteQuotientProjection R G K) x y

/-- Projection from the open-finite quotient limit, composed with the comparison from the
completion, recovers the corresponding completed projection. -/
@[simp]
theorem openFiniteLimitProjection_comp_fromCompleted
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    (completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K).comp
        (completedGroupAlgebraToOpenFiniteQuotientLimitRingHom R G) =
      completedGroupAlgebraOpenFiniteQuotientProjection R G K := by
  apply RingHom.ext
  intro x
  rfl

/--
Composing the comparison map with the dense map from the abstract group algebra recovers the
canonical completed group-algebra map.
-/
@[simp]
theorem completedGAToOpenFiniteQuotientLimitRingHom_comp_toCompletedGA :
    (completedGroupAlgebraToOpenFiniteQuotientLimitRingHom R G).comp
        (toCompletedGroupAlgebraRingHom R G) =
      toCompletedGroupAlgebraOpenFiniteQuotientLimitRingHom R G := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraToOpenFiniteQuotientLimit_toCompletedGroupAlgebra (R := R) (G := G) x

/-- The comparison map \(\widehat{R[G]} \to \varprojlim_{I,U} (R/I)[G/U]\) is continuous. -/
theorem continuous_completedGroupAlgebraToOpenFiniteQuotientLimit :
    Continuous (completedGroupAlgebraToOpenFiniteQuotientLimit R G) := by
  let S := completedGroupAlgebraOpenFiniteQuotientSystem R G
  let : ∀ K, TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    fun K => (completedGroupAlgebraOpenFiniteQuotientSystem R G).topologicalSpace K
  let π : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      CompletedGroupAlgebraCarrier R G →
        CompletedGroupAlgebraOpenQuotientStage R G K :=
    fun K => completedGroupAlgebraOpenFiniteQuotientProjection R G K
  have hπ : ∀ K, Continuous (π K) := by
    intro K
    exact continuous_completedGroupAlgebraOpenFiniteQuotientProjection (R := R) (G := G) K
  have hcompat : S.CompatibleMaps π := by
    intro K L hKL
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraOpenFiniteQuotientTransition_comp_projection
          R G hKL))
      x
  change Continuous (S.inverseLimitLift π hcompat)
  exact S.continuous_inverseLimitLift π hπ hcompat

/--
The image of the map from the completed group algebra to the open-finite quotient limit is dense
in the target completed group-algebra object.
-/
theorem denseRange_completedGroupAlgebraToOpenFiniteQuotientLimit
    [Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    DenseRange (completedGroupAlgebraToOpenFiniteQuotientLimit R G) := by
  have hdense :
      DenseRange
        ((completedGroupAlgebraToOpenFiniteQuotientLimit R G) ∘
          (toCompletedGroupAlgebra R G)) := by
    have hcomp :
        (completedGroupAlgebraToOpenFiniteQuotientLimit R G) ∘
            (toCompletedGroupAlgebra R G) =
          toCompletedGroupAlgebraOpenFiniteQuotientLimit R G := by
      funext x
      exact completedGroupAlgebraToOpenFiniteQuotientLimit_toCompletedGroupAlgebra
        (R := R) (G := G) x
    rw [hcomp]
    exact denseRange_toCompletedGroupAlgebraOpenFiniteQuotientLimit
      (R := R) (G := G)
  exact DenseRange.of_comp hdense

/--
The comparison map to the two-parameter kernel-neighborhood limit is injective when the
coefficient ring is profinite. This is the completed-stage form of the kernel-intersection claim
in Lemma 5.3.5(a).
-/
theorem injective_completedGroupAlgebraToOpenFiniteQuotientLimit
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] :
    Function.Injective (completedGroupAlgebraToOpenFiniteQuotientLimit R G) := by
  intro x y hxy
  apply completedGroupAlgebra_ext (R := R) (G := G)
  intro U
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro q
  have hzero : (completedGroupAlgebraProjection R G U x -
        completedGroupAlgebraProjection R G U y).coeff q = 0 := by
    apply profiniteRing_eq_zero_of_forall_openIdeal_quotient_eq_zero (R := R)
    intro Iopen
    let K : CompletedGroupAlgebraOpenQuotientIndex R G := (OrderDual.toDual Iopen, U)
    have hcoord := congrArg
      (fun z : CompletedGroupAlgebraOpenFiniteQuotientLimit R G =>
        completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K z) hxy
    change completedGroupAlgebraStageCoeffQuotientMap R G Iopen.1 U
        (completedGroupAlgebraProjection R G U x) =
      completedGroupAlgebraStageCoeffQuotientMap R G Iopen.1 U
        (completedGroupAlgebraProjection R G U y) at hcoord
    have hdiff : completedGroupAlgebraStageCoeffQuotientMap R G Iopen.1 U
        (completedGroupAlgebraProjection R G U x -
          completedGroupAlgebraProjection R G U y) = 0 := by
      rw [map_sub, hcoord, sub_self]
    have hq := congrArg
      (fun z : CompletedGroupAlgebraCoeffQuotientStage R G Iopen.1 U => z.coeff q) hdiff
    simpa [completedGroupAlgebraStageCoeffQuotientMap,
      MonoidAlgebra.coeff_mapRingHom] using hq
  have hsub : (completedGroupAlgebraProjection R G U x).coeff q -
      (completedGroupAlgebraProjection R G U y).coeff q = 0 := by
    exact hzero
  exact sub_eq_zero.mp hsub

/--
For profinite coefficients, the comparison map to the Hausdorff two-parameter
kernel-neighborhood limit has compact closed dense image and is surjective.
-/
theorem surjective_completedGroupAlgebraToOpenFiniteQuotientLimit
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Nonempty
        (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    Function.Surjective (completedGroupAlgebraToOpenFiniteQuotientLimit R G) := by
  let : CompactSpace (CompletedGroupAlgebraCarrier R G) :=
    completedGroupAlgebra_compactSpace (R := R) (G := G)
  let : T2Space (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
    completedGroupAlgebraOpenFiniteQuotientLimit_t2Space (R := R) (G := G)
  have hclosed : IsClosed (Set.range (completedGroupAlgebraToOpenFiniteQuotientLimit R G)) := by
    exact (isCompact_range
      (continuous_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G))).isClosed
  have hdense :
      closure (Set.range (completedGroupAlgebraToOpenFiniteQuotientLimit R G)) = Set.univ :=
    (denseRange_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G)).closure_range
  have hrange : Set.range (completedGroupAlgebraToOpenFiniteQuotientLimit R G) = Set.univ := by
    rwa [hclosed.closure_eq] at hdense
  intro y
  have hy : y ∈ Set.range (completedGroupAlgebraToOpenFiniteQuotientLimit R G) := by
    rw [hrange]
    exact Set.mem_univ y
  simpa using hy

/--
The comparison map \(\widehat{R[G]} \to \varprojlim_{I,U} (R/I)[G/U]\) is a bijection under the
profinite coefficient hypothesis.
-/
theorem bijective_completedGroupAlgebraToOpenFiniteQuotientLimit
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Nonempty
        (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    Function.Bijective (completedGroupAlgebraToOpenFiniteQuotientLimit R G) :=
  ⟨injective_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G),
    surjective_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G)⟩

/--
Ribes--Zalesskii Section \(5.3\) comparison: the fixed-coefficient inverse-limit model
\(\widehat{R[G]}\) is ring-isomorphic to the two-parameter kernel-neighborhood limit
\(\varprojlim_{I,U} (R/I)[G/U]\) for profinite coefficient rings.
-/
def completedGroupAlgebraOpenFiniteQuotientLimitRingEquiv
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Nonempty
        (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    CompletedGroupAlgebraCarrier R G ≃+* CompletedGroupAlgebraOpenFiniteQuotientLimit R G :=
  RingEquiv.ofBijective (completedGroupAlgebraToOpenFiniteQuotientLimitRingHom R G)
    (bijective_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G))

/--
The comparison equivalence is evaluated by the underlying all-finite or \(C\)-indexed comparison
map.
-/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitRingEquiv_apply
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Nonempty
        (CompletedGroupAlgebraOpenQuotientIndex R G)]
    (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraOpenFiniteQuotientLimitRingEquiv (R := R) (G := G) x =
      completedGroupAlgebraToOpenFiniteQuotientLimit R G x :=
  rfl

/--
The fixed-coefficient completed group algebra is homeomorphic to the two-parameter open finite
quotient inverse limit.
-/
def completedGroupAlgebraOpenFiniteQuotientLimitHomeomorph
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Nonempty
        (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    CompletedGroupAlgebraCarrier R G ≃ₜ CompletedGroupAlgebraOpenFiniteQuotientLimit R G := by
  letI : CompactSpace (CompletedGroupAlgebraCarrier R G) :=
    completedGroupAlgebra_compactSpace (R := R) (G := G)
  letI : T2Space (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
    completedGroupAlgebraOpenFiniteQuotientLimit_t2Space (R := R) (G := G)
  let e : CompletedGroupAlgebraCarrier R G ≃ CompletedGroupAlgebraOpenFiniteQuotientLimit R G :=
    (completedGroupAlgebraOpenFiniteQuotientLimitRingEquiv (R := R) (G := G)).toEquiv
  exact Continuous.homeoOfEquivCompactToT2 (f := e) (by
    change Continuous (completedGroupAlgebraToOpenFiniteQuotientLimit R G)
    exact continuous_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G))

/--
In Lemma 5.3.5(c), fixed-coefficient inverse-limit form, the abstract group algebra maps dense
into the completed group algebra.
-/
theorem denseRange_toCompletedGroupAlgebra :
    DenseRange (toCompletedGroupAlgebra R G) := by
  let S := completedGroupAlgebraSystem R G
  let : TopologicalSpace (MonoidAlgebra R G) := ⊥
  let : Nonempty (CompletedGroupAlgebraIndex G) := inferInstance
  have hdir : Directed (α := CompletedGroupAlgebraIndex G) (· ≤ ·) fun U => U :=
    directed_openNormalSubgroupInClass
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          ProCGroups.FiniteGroupClass.allFinite_formation
  have hdense :
      DenseRange
        (S.inverseLimitLift (fun U : CompletedGroupAlgebraIndex G =>
            completedGroupAlgebraStageMap R G U)
          (completedGroupAlgebraStageMap_compatibleMaps (R := R) (G := G))) :=
    S.denseRange_lift
      (fun U : CompletedGroupAlgebraIndex G => completedGroupAlgebraStageMap R G U)
      (completedGroupAlgebraStageMap_compatibleMaps (R := R) (G := G))
      (fun U => completedGroupAlgebraStageMap_surjective (R := R) (G := G) U)
      hdir
  change DenseRange
    (S.inverseLimitLift
      (fun U : CompletedGroupAlgebraIndex G => completedGroupAlgebraStageMap R G U)
      (completedGroupAlgebraStageMap_compatibleMaps (R := R) (G := G)))
  exact hdense

/-- The image of the canonical ring homomorphism into the completed group algebra is dense. -/
theorem denseRange_toCompletedGroupAlgebraRingHom :
    DenseRange (toCompletedGroupAlgebraRingHom R G) := by
  simpa [toCompletedGroupAlgebraRingHom] using
    denseRange_toCompletedGroupAlgebra (R := R) (G := G)

/--
The completion topology on the abstract group algebra, induced by the canonical map into
\(\widehat{R[G]}\); below it is identified with the kernel-neighborhood topology generated by
the maps \(R[G] \to (R/I)[G/U]\).
-/
@[reducible]
def completedGroupAlgebraNaturalTopology (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    TopologicalSpace (MonoidAlgebra R G) :=
  TopologicalSpace.induced (toCompletedGroupAlgebra R G) inferInstance

/-- A genuine copy of the abstract group algebra reserved for the topology induced by the
canonical map into `[[R G]]`.

This is deliberately a structure, not a reducible type synonym: the natural and
kernel-neighborhood topologies therefore cannot compete as instances on the same type. -/
@[ext]
structure CompletedGroupAlgebraNaturalSource (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] where
  /-- The group-algebra element carried by the natural-topology wrapper. -/
  toMonoidAlgebra : MonoidAlgebra R G

/-- Forget the natural-topology wrapper. -/
def completedGroupAlgebraNaturalSourceEquiv :
    CompletedGroupAlgebraNaturalSource R G ≃ MonoidAlgebra R G where
  toFun := CompletedGroupAlgebraNaturalSource.toMonoidAlgebra
  invFun := fun x => CompletedGroupAlgebraNaturalSource.mk x
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- Transport the group-algebra ring structure to its natural-topology wrapper. -/
instance instRingCompletedGroupAlgebraNaturalSource :
    Ring (CompletedGroupAlgebraNaturalSource R G) :=
  (completedGroupAlgebraNaturalSourceEquiv (R := R) (G := G)).ring

/-- Algebraic form of the forgetful equivalence from the natural-topology source. -/
def completedGroupAlgebraNaturalSourceRingEquiv :
    CompletedGroupAlgebraNaturalSource R G ≃+* MonoidAlgebra R G :=
  (completedGroupAlgebraNaturalSourceEquiv (R := R) (G := G)).ringEquiv

/-- Insert a raw group-algebra element into the natural-topology source.  Keeping this as a
bundled ring homomorphism avoids making downstream APIs unpack the topology wrapper. -/
def completedGroupAlgebraNaturalSourceOf :
    MonoidAlgebra R G →+* CompletedGroupAlgebraNaturalSource R G :=
  (completedGroupAlgebraNaturalSourceRingEquiv (R := R) (G := G)).symm.toRingHom

/-- Forgetting the natural-topology wrapper after inserting a group-algebra element returns that
element. -/
@[simp]
theorem completedGroupAlgebraNaturalSourceOf_toMonoidAlgebra (x : MonoidAlgebra R G) :
    (completedGroupAlgebraNaturalSourceOf (R := R) (G := G) x).toMonoidAlgebra = x :=
  by
    change (completedGroupAlgebraNaturalSourceRingEquiv (R := R) (G := G))
      ((completedGroupAlgebraNaturalSourceRingEquiv (R := R) (G := G)).symm x) = x
    exact (completedGroupAlgebraNaturalSourceRingEquiv (R := R) (G := G)).apply_symm_apply x

/-- The coefficient-ring embedding into the natural-topology source. -/
def completedGroupAlgebraNaturalSourceCoefficientRingHom :
    R →+* CompletedGroupAlgebraNaturalSource R G :=
  (completedGroupAlgebraNaturalSourceOf (R := R) (G := G)).comp
    (MonoidAlgebra.singleOneRingHom (R := R) (M := G))

/-- The group-like embedding into the natural-topology source. -/
def completedGroupAlgebraNaturalSourceGroupMonoidHom :
    G →* CompletedGroupAlgebraNaturalSource R G :=
  (completedGroupAlgebraNaturalSourceOf (R := R) (G := G)).toMonoidHom.comp
    (MonoidAlgebra.of R G)

/-- The same group-like map with its invertibility recorded in the codomain. -/
def completedGroupAlgebraNaturalSourceGroupUnitsHom :
    G →* (CompletedGroupAlgebraNaturalSource R G)ˣ :=
  (completedGroupAlgebraNaturalSourceGroupMonoidHom (R := R) (G := G)).toHomUnits

/-- Forgetting invertibility from the group-like units map gives the group-like monoid map. -/
@[simp]
theorem completedGroupAlgebraNaturalSourceGroupUnitsHom_coe (g : G) :
    ((completedGroupAlgebraNaturalSourceGroupUnitsHom (R := R) (G := G) g :
        (CompletedGroupAlgebraNaturalSource R G)ˣ) :
      CompletedGroupAlgebraNaturalSource R G) =
      completedGroupAlgebraNaturalSourceGroupMonoidHom (R := R) (G := G) g :=
  rfl

/-- The wrapped coefficient embedding forgets to the group algebra's scalar at the identity. -/
@[simp]
theorem completedGroupAlgebraNaturalSourceCoefficientRingHom_toMonoidAlgebra (r : R) :
    (completedGroupAlgebraNaturalSourceCoefficientRingHom (R := R) (G := G) r).toMonoidAlgebra =
      MonoidAlgebra.single 1 r := by
  simp [completedGroupAlgebraNaturalSourceCoefficientRingHom,
    MonoidAlgebra.singleOneRingHom]

/-- The wrapped group-like embedding forgets to the usual group-algebra basis element. -/
@[simp]
theorem completedGroupAlgebraNaturalSourceGroupMonoidHom_toMonoidAlgebra (g : G) :
    (completedGroupAlgebraNaturalSourceGroupMonoidHom (R := R) (G := G) g).toMonoidAlgebra =
      MonoidAlgebra.of R G g := by
  simp [completedGroupAlgebraNaturalSourceGroupMonoidHom]

/-- Equip the natural-source wrapper with the topology induced by the completed group
algebra. -/
instance instTopologicalSpaceCompletedGroupAlgebraNaturalSource :
    TopologicalSpace (CompletedGroupAlgebraNaturalSource R G) := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    completedGroupAlgebraNaturalTopology R G
  exact (completedGroupAlgebraNaturalSourceEquiv (R := R) (G := G)).topologicalSpace

/-- The forgetful equivalence is a homeomorphism to the raw group algebra carrying the natural
topology. -/
def completedGroupAlgebraNaturalSourceHomeomorph :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      completedGroupAlgebraNaturalTopology R G
    CompletedGroupAlgebraNaturalSource R G ≃ₜ MonoidAlgebra R G := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    completedGroupAlgebraNaturalTopology R G
  exact (completedGroupAlgebraNaturalSourceEquiv (R := R) (G := G)).homeomorph

/-- A genuine copy of the abstract group algebra reserved for the open-ideal/finite-group
kernel-neighborhood topology. -/
@[ext]
structure CompletedGroupAlgebraKernelSource (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] where
  /-- The group-algebra element carried by the kernel-neighborhood-topology wrapper. -/
  toMonoidAlgebra : MonoidAlgebra R G

/-- Forget the kernel-neighborhood-topology wrapper. -/
def completedGroupAlgebraKernelSourceEquiv :
    CompletedGroupAlgebraKernelSource R G ≃ MonoidAlgebra R G where
  toFun := CompletedGroupAlgebraKernelSource.toMonoidAlgebra
  invFun := fun x => CompletedGroupAlgebraKernelSource.mk x
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- Transport the group-algebra ring structure to its kernel-neighborhood wrapper. -/
instance instRingCompletedGroupAlgebraKernelSource :
    Ring (CompletedGroupAlgebraKernelSource R G) :=
  (completedGroupAlgebraKernelSourceEquiv (R := R) (G := G)).ring

/-- Algebraic form of the forgetful equivalence from the kernel-neighborhood source. -/
def completedGroupAlgebraKernelSourceRingEquiv :
    CompletedGroupAlgebraKernelSource R G ≃+* MonoidAlgebra R G :=
  (completedGroupAlgebraKernelSourceEquiv (R := R) (G := G)).ringEquiv

/-- Equip the kernel-source wrapper with the open-finite-quotient kernel topology. -/
instance instTopologicalSpaceCompletedGroupAlgebraKernelSource :
    TopologicalSpace (CompletedGroupAlgebraKernelSource R G) := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  exact (completedGroupAlgebraKernelSourceEquiv (R := R) (G := G)).topologicalSpace

/-- The forgetful equivalence is a homeomorphism to the raw group algebra carrying the
kernel-neighborhood topology. -/
def completedGroupAlgebraKernelSourceHomeomorph :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    CompletedGroupAlgebraKernelSource R G ≃ₜ MonoidAlgebra R G := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  exact (completedGroupAlgebraKernelSourceEquiv (R := R) (G := G)).homeomorph

/-- Canonical map from the natural-topology source wrapper. -/
def toCompletedGroupAlgebraNaturalSourceRingHom :
    CompletedGroupAlgebraNaturalSource R G →+* CompletedGroupAlgebraCarrier R G :=
  (toCompletedGroupAlgebraRingHom R G).comp
    (completedGroupAlgebraNaturalSourceRingEquiv (R := R) (G := G)).toRingHom

/-- On coefficients, the wrapped canonical map is the completed algebra's scalar map. -/
@[simp]
theorem toCompletedGroupAlgebraNaturalSourceRingHom_coefficient (r : R) :
    toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G)
        (completedGroupAlgebraNaturalSourceCoefficientRingHom (R := R) (G := G) r) =
      algebraMap R (CompletedGroupAlgebraCarrier R G) r := by
  change toCompletedGroupAlgebra R G
      (completedGroupAlgebraNaturalSourceCoefficientRingHom (R := R) (G := G) r).toMonoidAlgebra =
    algebraMap R (CompletedGroupAlgebraCarrier R G) r
  rw [completedGroupAlgebraNaturalSourceCoefficientRingHom_toMonoidAlgebra]
  apply completedGroupAlgebra_ext (R := R) (G := G)
  intro U
  change completedGroupAlgebraStageMap R G U (MonoidAlgebra.single 1 r) =
    algebraMap R (CompletedGroupAlgebraStage R G U) r
  simpa only [MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
    RingHom.coe_id, Function.comp_apply, id_eq] using
    completedGroupAlgebraStageMap_algebraMap (R := R) (G := G) U r

/-- On group-like elements, the wrapped canonical map is the usual completed group element. -/
@[simp]
theorem toCompletedGroupAlgebraNaturalSourceRingHom_group (g : G) :
    toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G)
        (completedGroupAlgebraNaturalSourceGroupMonoidHom (R := R) (G := G) g) =
      toCompletedGroupAlgebra R G (MonoidAlgebra.of R G g) := by
  change toCompletedGroupAlgebra R G
      (completedGroupAlgebraNaturalSourceGroupMonoidHom (R := R) (G := G) g).toMonoidAlgebra =
    toCompletedGroupAlgebra R G (MonoidAlgebra.of R G g)
  rw [completedGroupAlgebraNaturalSourceGroupMonoidHom_toMonoidAlgebra]

/--
The dense map from the abstract group algebra to the completed group algebra is continuous for
the natural finite-quotient topology.
-/
theorem continuous_toCompletedGroupAlgebraRingHom_naturalTopology :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      completedGroupAlgebraNaturalTopology R G
    Continuous (toCompletedGroupAlgebraRingHom R G) := by
  let : TopologicalSpace (MonoidAlgebra R G) :=
    completedGroupAlgebraNaturalTopology R G
  change Continuous (toCompletedGroupAlgebra R G)
  exact (continuous_induced_dom : Continuous (toCompletedGroupAlgebra R G))

/-- The natural-source wrapper's canonical map is continuous by construction. -/
theorem continuous_toCompletedGroupAlgebraNaturalSourceRingHom :
    Continuous (toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G)) := by
  let : TopologicalSpace (MonoidAlgebra R G) :=
    completedGroupAlgebraNaturalTopology R G
  exact
    (continuous_toCompletedGroupAlgebraRingHom_naturalTopology (R := R) (G := G)).comp
      (completedGroupAlgebraNaturalSourceHomeomorph (R := R) (G := G)).continuous

/-- The natural-source wrapper has the same dense image as the raw algebraic group ring. -/
theorem denseRange_toCompletedGroupAlgebraNaturalSourceRingHom
    : DenseRange (toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G)) := by
  let : TopologicalSpace (MonoidAlgebra R G) :=
    completedGroupAlgebraNaturalTopology R G
  simpa [toCompletedGroupAlgebraNaturalSourceRingHom, Function.comp_def] using
    (denseRange_toCompletedGroupAlgebraRingHom (R := R) (G := G)).comp
      (completedGroupAlgebraNaturalSourceRingEquiv
        (R := R) (G := G)).surjective.denseRange
      (continuous_toCompletedGroupAlgebraRingHom_naturalTopology (R := R) (G := G))

/-- A finite-stage group-algebra map with the natural-topology source kept explicit in its type. -/
def completedGroupAlgebraNaturalSourceStageMap (U : CompletedGroupAlgebraIndex G) :
    CompletedGroupAlgebraNaturalSource R G →+* CompletedGroupAlgebraStage R G U :=
  (completedGroupAlgebraStageMap R G U).comp
    (completedGroupAlgebraNaturalSourceRingEquiv (R := R) (G := G)).toRingHom

/-- The finite-stage map from the natural-source wrapper is the ordinary stage map after
forgetting the wrapper. -/
@[simp]
theorem completedGroupAlgebraNaturalSourceStageMap_apply
    (U : CompletedGroupAlgebraIndex G) (x : CompletedGroupAlgebraNaturalSource R G) :
    completedGroupAlgebraNaturalSourceStageMap R G U x =
      completedGroupAlgebraStageMap R G U x.toMonoidAlgebra := by
  change completedGroupAlgebraStageMap R G U
      ((completedGroupAlgebraNaturalSourceRingEquiv (R := R) (G := G)) x) =
    completedGroupAlgebraStageMap R G U x.toMonoidAlgebra
  rfl

/--
The canonical map as a continuous \(R\)-linear map for the topology induced from
\(\widehat{R[G]}\).
-/
def toCompletedGroupAlgebraContinuousLinearMap_naturalTopology :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      completedGroupAlgebraNaturalTopology R G
    MonoidAlgebra R G →L[R] CompletedGroupAlgebraCarrier R G := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    completedGroupAlgebraNaturalTopology R G
  exact
    { toLinearMap := toCompletedGroupAlgebraLinearMap R G
      cont := continuous_toCompletedGroupAlgebraRingHom_naturalTopology (R := R) (G := G) }

omit [IsTopologicalRing R] in
/--
The kernel-neighborhood topology is exactly the topology induced by the canonical map from
\(R[G]\) to the two-parameter kernel-neighborhood limit.
-/
theorem groupAlgebraOpenFiniteQuotientKernelTopology_eq_induced_toLimit :
    groupAlgebraOpenFiniteQuotientKernelTopology R G =
      TopologicalSpace.induced (toCompletedGroupAlgebraOpenFiniteQuotientLimit R G)
          inferInstance := by
  let S := completedGroupAlgebraOpenFiniteQuotientSystem R G
  let : ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
      TopologicalSpace (CompletedGroupAlgebraOpenQuotientStage R G K) :=
    fun K => completedGroupAlgebraOpenFiniteQuotientStageTopology R G K
  change TopologicalSpace.induced (groupAlgebraOpenFiniteQuotientProductMap R G) inferInstance =
    TopologicalSpace.induced (toCompletedGroupAlgebraOpenFiniteQuotientLimit R G)
      (TopologicalSpace.induced
        (fun z : CompletedGroupAlgebraOpenFiniteQuotientLimit R G => z.1) inferInstance)
  rw [induced_compose]
  rfl

/--
Under the profinite coefficient hypothesis, the topology on \(R[G]\) induced from
\(\widehat{R[G]}\) agrees with the topology induced by the two-parameter kernel-neighborhood
limit.
-/
theorem completedGroupAlgebraNaturalTopology_eq_induced_toOpenFiniteQuotientLimit
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Nonempty
        (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    completedGroupAlgebraNaturalTopology R G =
      TopologicalSpace.induced (toCompletedGroupAlgebraOpenFiniteQuotientLimit R G)
          inferInstance := by
  let e := completedGroupAlgebraOpenFiniteQuotientLimitHomeomorph (R := R) (G := G)
  have hcomp : e ∘ toCompletedGroupAlgebra R G =
      toCompletedGroupAlgebraOpenFiniteQuotientLimit R G := by
    funext x
    exact completedGroupAlgebraToOpenFiniteQuotientLimit_toCompletedGroupAlgebra
      (R := R) (G := G) x
  dsimp [completedGroupAlgebraNaturalTopology]
  rw [e.isInducing.eq_induced]
  rw [induced_compose]
  rw [hcomp]

/--
Ribes--Zalesskii Section \(5.3\) natural topology comparison: the topology on the abstract group
algebra induced from \(\widehat{R[G]}\) is the kernel-neighborhood topology generated by the
maps \(R[G] \to (R/I)[G/U]\).
-/
theorem completedGroupAlgebraNaturalTopology_eq_openFiniteQuotientKernelTopology
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Nonempty
        (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    completedGroupAlgebraNaturalTopology R G =
      groupAlgebraOpenFiniteQuotientKernelTopology R G := by
  rw [completedGroupAlgebraNaturalTopology_eq_induced_toOpenFiniteQuotientLimit
      (R := R) (G := G),
    groupAlgebraOpenFiniteQuotientKernelTopology_eq_induced_toLimit (R := R) (G := G)]

/-- The two source wrappers are canonically homeomorphic once the coefficient ring is profinite. -/
def completedGroupAlgebraNaturalSourceHomeomorphKernelSource
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Nonempty
        (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    CompletedGroupAlgebraNaturalSource R G ≃ₜ CompletedGroupAlgebraKernelSource R G where
  toEquiv :=
    (completedGroupAlgebraNaturalSourceEquiv (R := R) (G := G)).trans
      (completedGroupAlgebraKernelSourceEquiv (R := R) (G := G)).symm
  continuous_toFun := by
    let τnat := completedGroupAlgebraNaturalTopology R G
    let τker := groupAlgebraOpenFiniteQuotientKernelTopology R G
    have hτ : τnat = τker :=
      completedGroupAlgebraNaturalTopology_eq_openFiniteQuotientKernelTopology
        (R := R) (G := G)
    have hforget :
        @Continuous (CompletedGroupAlgebraNaturalSource R G) (MonoidAlgebra R G)
          inferInstance τnat
          (completedGroupAlgebraNaturalSourceEquiv (R := R) (G := G)) := by
      let : TopologicalSpace (MonoidAlgebra R G) := τnat
      exact
        (completedGroupAlgebraNaturalSourceHomeomorph (R := R) (G := G)).continuous
    have hid : @Continuous (MonoidAlgebra R G) (MonoidAlgebra R G) τnat τker id := by
      rw [hτ]
      exact continuous_id
    have hwrap :
        @Continuous (MonoidAlgebra R G) (CompletedGroupAlgebraKernelSource R G)
          τker inferInstance
          (completedGroupAlgebraKernelSourceEquiv (R := R) (G := G)).symm :=
      (completedGroupAlgebraKernelSourceHomeomorph (R := R) (G := G)).symm.continuous
    have hraw :=
      @Continuous.comp
        (CompletedGroupAlgebraNaturalSource R G) (MonoidAlgebra R G) (MonoidAlgebra R G)
        inferInstance τnat τker
        (completedGroupAlgebraNaturalSourceEquiv (R := R) (G := G)) id hid hforget
    have htotal :=
      @Continuous.comp
        (CompletedGroupAlgebraNaturalSource R G) (MonoidAlgebra R G)
        (CompletedGroupAlgebraKernelSource R G)
        inferInstance τker inferInstance
        (id ∘ completedGroupAlgebraNaturalSourceEquiv (R := R) (G := G))
        (completedGroupAlgebraKernelSourceEquiv (R := R) (G := G)).symm hwrap hraw
    change Continuous
      ((completedGroupAlgebraKernelSourceEquiv (R := R) (G := G)).symm ∘ id ∘
        (completedGroupAlgebraNaturalSourceEquiv (R := R) (G := G)))
    exact htotal
  continuous_invFun := by
    let τnat := completedGroupAlgebraNaturalTopology R G
    let τker := groupAlgebraOpenFiniteQuotientKernelTopology R G
    have hτ : τnat = τker :=
      completedGroupAlgebraNaturalTopology_eq_openFiniteQuotientKernelTopology
        (R := R) (G := G)
    have hforget :
        @Continuous (CompletedGroupAlgebraKernelSource R G) (MonoidAlgebra R G)
          inferInstance τker
          (completedGroupAlgebraKernelSourceEquiv (R := R) (G := G)) :=
      (completedGroupAlgebraKernelSourceHomeomorph (R := R) (G := G)).continuous
    have hid : @Continuous (MonoidAlgebra R G) (MonoidAlgebra R G) τker τnat id := by
      rw [hτ]
      exact continuous_id
    have hwrap :
        @Continuous (MonoidAlgebra R G) (CompletedGroupAlgebraNaturalSource R G)
          τnat inferInstance
          (completedGroupAlgebraNaturalSourceEquiv (R := R) (G := G)).symm := by
      let : TopologicalSpace (MonoidAlgebra R G) := τnat
      exact
        (completedGroupAlgebraNaturalSourceHomeomorph (R := R) (G := G)).symm.continuous
    have hraw :=
      @Continuous.comp
        (CompletedGroupAlgebraKernelSource R G) (MonoidAlgebra R G) (MonoidAlgebra R G)
        inferInstance τker τnat
        (completedGroupAlgebraKernelSourceEquiv (R := R) (G := G)) id hid hforget
    have htotal :=
      @Continuous.comp
        (CompletedGroupAlgebraKernelSource R G) (MonoidAlgebra R G)
        (CompletedGroupAlgebraNaturalSource R G)
        inferInstance τnat inferInstance
        (id ∘ completedGroupAlgebraKernelSourceEquiv (R := R) (G := G))
        (completedGroupAlgebraNaturalSourceEquiv (R := R) (G := G)).symm hwrap hraw
    change Continuous
      ((completedGroupAlgebraNaturalSourceEquiv (R := R) (G := G)).symm ∘ id ∘
        (completedGroupAlgebraKernelSourceEquiv (R := R) (G := G)))
    exact htotal

/-- Canonical map from the kernel-neighborhood source wrapper. -/
def toCompletedGroupAlgebraKernelSourceRingHom :
    CompletedGroupAlgebraKernelSource R G →+* CompletedGroupAlgebraCarrier R G :=
  (toCompletedGroupAlgebraRingHom R G).comp
    (completedGroupAlgebraKernelSourceRingEquiv (R := R) (G := G)).toRingHom

/--
The canonical map \(R[G] \to \widehat{R[G]}\) is continuous for the kernel-neighborhood topology
on \(R[G]\).
-/
theorem continuous_toCompletedGroupAlgebraRingHom_kernelTopology
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Nonempty
        (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    Continuous (toCompletedGroupAlgebraRingHom R G) := by
  let τnat := completedGroupAlgebraNaturalTopology R G
  let τker := groupAlgebraOpenFiniteQuotientKernelTopology R G
  have hτ : τnat = τker :=
    completedGroupAlgebraNaturalTopology_eq_openFiniteQuotientKernelTopology
      (R := R) (G := G)
  change @Continuous (MonoidAlgebra R G) (CompletedGroupAlgebraCarrier R G)
    τker inferInstance (toCompletedGroupAlgebraRingHom R G)
  rw [← hτ]
  exact continuous_toCompletedGroupAlgebraRingHom_naturalTopology (R := R) (G := G)

/-- The kernel-wrapper canonical map is continuous under the profinite coefficient hypothesis. -/
theorem continuous_toCompletedGroupAlgebraKernelSourceRingHom
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Nonempty
        (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    Continuous (toCompletedGroupAlgebraKernelSourceRingHom (R := R) (G := G)) := by
  let : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  exact
    (continuous_toCompletedGroupAlgebraRingHom_kernelTopology (R := R) (G := G)).comp
      (completedGroupAlgebraKernelSourceHomeomorph (R := R) (G := G)).continuous

/-- The canonical map as a continuous \(R\)-linear map for the kernel-neighborhood topology. -/
def toCompletedGroupAlgebraContinuousLinearMap_kernelTopology
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Nonempty
        (CompletedGroupAlgebraOpenQuotientIndex R G)] :
    letI : TopologicalSpace (MonoidAlgebra R G) :=
      groupAlgebraOpenFiniteQuotientKernelTopology R G
    MonoidAlgebra R G →L[R] CompletedGroupAlgebraCarrier R G := by
  letI : TopologicalSpace (MonoidAlgebra R G) :=
    groupAlgebraOpenFiniteQuotientKernelTopology R G
  exact
    { toLinearMap := toCompletedGroupAlgebraLinearMap R G
      cont := continuous_toCompletedGroupAlgebraRingHom_kernelTopology
        (R := R) (G := G) }

end

end CompletedGroupAlgebra
