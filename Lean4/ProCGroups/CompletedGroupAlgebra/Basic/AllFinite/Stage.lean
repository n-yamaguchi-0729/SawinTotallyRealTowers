import ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Index
import ProCGroups.Completion.ProCInteger

set_option autoImplicit false

/-!
# Completed Group Algebra / Basic / All Finite / Stage

This module defines the finite group-algebra stages \(R[G/U]\), coefficient-change maps,
quotient-transition ring homomorphisms, their compatibility laws, and the topological inverse
system used by the all-finite completion.
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
variable (R : Type u) [CommRing R]

/-- The finite-stage group algebra \(R[G/U]\) from Ribes--Zalesskii, Section 5.3. -/
abbrev CompletedGroupAlgebraStage (R : Type u) (G : Type v) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndex G) :
    Type (max u v) :=
  MonoidAlgebra R (CompletedGroupAlgebraQuotient G U)

/--
For a homomorphism \(f:R\to S\), coefficient change at a fixed finite stage sends \(R[G/U]\) to
\(S[G/U]\) by applying \(f\) to each coefficient and leaving the quotient support unchanged.
-/
def completedGroupAlgebraStageCoeffMap
    (S : Type w) [CommRing S] (f : R →+* S) (U : CompletedGroupAlgebraIndex G) :
    CompletedGroupAlgebraStage R G U →+* CompletedGroupAlgebraStage S G U :=
  MonoidAlgebra.mapRingHom (CompletedGroupAlgebraQuotient G U) f

/--
The coefficient-change map on a finite stage sends the singleton basis function supported at
\(q\) with coefficient \(r\) to the singleton supported at the same \(q\) with coefficient
\(f(r)\).
-/
@[simp]
theorem completedGroupAlgebraStageCoeffMap_single
    (S : Type w) [CommRing S] (f : R →+* S) (U : CompletedGroupAlgebraIndex G)
    (q : CompletedGroupAlgebraQuotient G U) (r : R) :
    completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single q (f r) := by
  exact MonoidAlgebra.mapRingHom_single f q r

/--
At an all-finite stage \(U\), changing coefficients first along \(f\) and then along \(g\) equals
changing coefficients along \(g\circ f\).
-/
@[simp]
theorem completedGroupAlgebraStageCoeffMap_comp
    (S : Type w) (T : Type*) [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (U : CompletedGroupAlgebraIndex G) :
    (completedGroupAlgebraStageCoeffMap (R := S) (G := G) T g U).comp
        (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U) =
      completedGroupAlgebraStageCoeffMap (R := R) (G := G) T (g.comp f) U := by
  exact (MonoidAlgebra.mapRingHom_comp
    (M := CompletedGroupAlgebraQuotient G U) g f).symm

/-- A finite coefficient ring gives finite all-finite completed-group-algebra stages. -/
theorem finite_completedGroupAlgebraStage [Finite R] (U : CompletedGroupAlgebraIndex G) :
    Finite (CompletedGroupAlgebraStage R G U) := by
  classical
  let f : CompletedGroupAlgebraStage R G U → CompletedGroupAlgebraQuotient G U → R :=
    fun x q => x.coeff q
  refine Finite.of_injective f ?_
  intro x y hxy
  ext q
  exact congrFun hxy q

/-- The transition map \(R[G/V] \to R[G/U]\) is induced by the quotient map \(G/V \to G/U\). -/
def completedGroupAlgebraTransition (R : Type u) (G : Type v) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {U V : CompletedGroupAlgebraIndex G}
    (hUV : U ≤ V) :
    CompletedGroupAlgebraStage R G V →+* CompletedGroupAlgebraStage R G U :=
  MonoidAlgebra.mapDomainRingHom R
    (OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)

/-- The transition map sends a basis element to the induced basis element. -/
@[simp]
theorem completedGroupAlgebraTransition_of
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V)
    (g : CompletedGroupAlgebraQuotient G V) :
    completedGroupAlgebraTransition R G hUV (MonoidAlgebra.of R _ g) =
      MonoidAlgebra.single ((OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) g) 1 := by
  classical
  change
    MonoidAlgebra.mapDomain
        (OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) g) 1
  exact MonoidAlgebra.mapDomain_single

/--
The transition map \(R[G/V] \to R[G/U]\) sends a singleton supported at a class of \(G/V\) to
the singleton supported at its image in \(G/U\), with the same coefficient.
-/
@[simp]
theorem completedGroupAlgebraTransition_single
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V)
    (q : CompletedGroupAlgebraQuotient G V) (r : R) :
    completedGroupAlgebraTransition R G hUV (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) r := by
  classical
  change
    MonoidAlgebra.mapDomain
        (OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) r
  exact MonoidAlgebra.mapDomain_single

/-- The transition map for the reflexive relation is the identity. -/
@[simp]
theorem completedGroupAlgebraTransition_id (U : CompletedGroupAlgebraIndex G) :
    completedGroupAlgebraTransition R G (le_rfl : U ≤ U) = RingHom.id _ := by
  rw [completedGroupAlgebraTransition, OpenNormalSubgroupInClass.map_id]
  exact MonoidAlgebra.mapDomainRingHom_id
    (R := R) (M := CompletedGroupAlgebraQuotient G U)

/-- Transition maps compose along refinements of finite quotients. -/
@[simp]
theorem completedGroupAlgebraTransition_comp
    {U V W : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) (hVW : V ≤ W) :
    (completedGroupAlgebraTransition R G hUV).comp
        (completedGroupAlgebraTransition R G hVW) =
      completedGroupAlgebraTransition R G (hUV.trans hVW) := by
  unfold completedGroupAlgebraTransition
  exact
    (MonoidAlgebra.mapDomainRingHom_comp (R := R)
      (OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
      (OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
        (U := OrderDual.ofDual V) (V := OrderDual.ofDual W) hVW)).symm.trans
      (congrArg (MonoidAlgebra.mapDomainRingHom R)
        (OpenNormalSubgroupInClass.map_comp
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) (W := OrderDual.ofDual W)
          hUV hVW))

/--
Coefficient change is performed stagewise: supports are unchanged and coefficients are
transported by the given ring homomorphism.
-/
@[simp]
theorem completedGroupAlgebraStageCoeffMap_compatible
    (S : Type w) [CommRing S] (f : R →+* S)
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U).comp
        (completedGroupAlgebraTransition R G hUV) =
      (completedGroupAlgebraTransition S G hUV).comp
        (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f V) := by
  exact MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
    (f := f)
    (g := OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)

/--
Two coefficient changes and two group-quotient transitions compose as the combined change and
combined transition.
-/
@[simp 900]
theorem completedGroupAlgebraStageCoeffMap_transition_comp
    (S : Type w) (T : Type*) [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    {U V W : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) (hVW : V ≤ W) :
    ((completedGroupAlgebraStageCoeffMap (R := S) (G := G) T g U).comp
        (completedGroupAlgebraTransition S G hUV)).comp
        ((completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f V).comp
          (completedGroupAlgebraTransition R G hVW)) =
      (completedGroupAlgebraStageCoeffMap (R := R) (G := G) T (g.comp f) U).comp
        (completedGroupAlgebraTransition R G (hUV.trans hVW)) := by
  calc
    ((completedGroupAlgebraStageCoeffMap (R := S) (G := G) T g U).comp
        (completedGroupAlgebraTransition S G hUV)).comp
        ((completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f V).comp
          (completedGroupAlgebraTransition R G hVW))
      =
    (completedGroupAlgebraStageCoeffMap (R := S) (G := G) T g U).comp
      (((completedGroupAlgebraTransition S G hUV).comp
        (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f V)).comp
        (completedGroupAlgebraTransition R G hVW)) := by
          apply RingHom.ext
          intro x
          rfl
    _ =
    (completedGroupAlgebraStageCoeffMap (R := S) (G := G) T g U).comp
      (((completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U).comp
        (completedGroupAlgebraTransition R G hUV)).comp
        (completedGroupAlgebraTransition R G hVW)) := by
          rw [← completedGroupAlgebraStageCoeffMap_compatible
            (R := R) (G := G) S f hUV]
    _ =
    ((completedGroupAlgebraStageCoeffMap (R := S) (G := G) T g U).comp
        (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U)).comp
      ((completedGroupAlgebraTransition R G hUV).comp
        (completedGroupAlgebraTransition R G hVW)) := by
          apply RingHom.ext
          intro x
          rfl
    _ =
    (completedGroupAlgebraStageCoeffMap (R := R) (G := G) T (g.comp f) U).comp
      ((completedGroupAlgebraTransition R G hUV).comp
        (completedGroupAlgebraTransition R G hVW)) := by
          rw [completedGroupAlgebraStageCoeffMap_comp]
    _ =
    (completedGroupAlgebraStageCoeffMap (R := R) (G := G) T (g.comp f) U).comp
      (completedGroupAlgebraTransition R G (hUV.trans hVW)) := by
        rw [completedGroupAlgebraTransition_comp]

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The inverse system \(U\mapsto R[G/U]\) with the finite product topology on each stage. -/
def completedGroupAlgebraSystem (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ProCGroups.InverseSystems.InverseSystem (I := CompletedGroupAlgebraIndex G) where
  X := CompletedGroupAlgebraStage R G
  topologicalSpace := fun U => finiteGroupAlgebraTopology R (CompletedGroupAlgebraQuotient G U)
  map := fun {U V} hUV => completedGroupAlgebraTransition R G hUV
  continuous_map := by
    intro U V hUV
    exact finiteGroupAlgebra_mapDomainRingHom_continuous R
      (CompletedGroupAlgebraQuotient G V) (CompletedGroupAlgebraQuotient G U)
      (OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
  map_id := by
    intro U
    funext x
    exact congrFun
      (congrArg DFunLike.coe (completedGroupAlgebraTransition_id (R := R) (G := G) U)) x
  map_comp := by
    intro U V W hUV hVW
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraTransition_comp (R := R) (G := G) hUV hVW)) x

end

end CompletedGroupAlgebra
