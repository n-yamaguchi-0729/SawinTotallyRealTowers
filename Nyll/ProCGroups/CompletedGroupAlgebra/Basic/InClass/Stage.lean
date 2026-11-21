/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.InClass.Index

/-!
# Completed Group Algebra / Basic / Within a Class / Stage

This module defines the \(C\)-indexed finite group-algebra stages, their transition and
coefficient-change ring homomorphisms, and the compatibility identities used by the inverse
system.
-/

@[expose] public section

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v w

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R]

section InClass

/-- A \(C\)-indexed quotient \(G/U\) determines the finite-stage group algebra \(R[G/U]\). -/
abbrev CompletedGroupAlgebraStageInClass (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndexInClass G C) :
    Type (max u v) :=
  MonoidAlgebra R (CompletedGroupAlgebraQuotientInClass G C U)

/--
The coefficient-change map on one \(C\)-indexed completed-group-algebra stage is defined by
changing coefficients.
-/
def completedGroupAlgebraStageCoeffMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (S : Type w) [CommRing S]
    (f : R →+* S) (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraStageInClass C R G U →+*
      CompletedGroupAlgebraStageInClass C S G U :=
  MonoidAlgebra.mapRingHom (CompletedGroupAlgebraQuotientInClass G C U) f

/--
At a \(C\)-indexed stage, coefficient change sends the singleton at \(q\) with coefficient \(r\)
to the singleton at \(q\) with coefficient \(f(r)\).
-/
@[simp]
theorem completedGroupAlgebraStageCoeffMapInClass_single
    (C : ProCGroups.FiniteGroupClass.{v}) (S : Type w) [CommRing S]
    (f : R →+* S) (U : CompletedGroupAlgebraIndexInClass G C)
    (q : CompletedGroupAlgebraQuotientInClass G C U) (r : R) :
    completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single q (f r) := by
  exact MonoidAlgebra.mapRingHom_single f q r

/--
At a \(C\)-indexed stage \(U\), changing coefficients first along \(f\) and then along \(g\)
equals changing coefficients along \(g\circ f\).
-/
@[simp]
theorem completedGroupAlgebraStageCoeffMapInClass_comp
    (C : ProCGroups.FiniteGroupClass.{v}) (S : Type w) (T : Type*) [CommRing S]
    [CommRing T] (f : R →+* S) (g : S →+* T)
    (U : CompletedGroupAlgebraIndexInClass G C) :
    (completedGroupAlgebraStageCoeffMapInClass (R := S) (G := G) C T g U).comp
        (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U) =
      completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C T (g.comp f) U := by
  exact (MonoidAlgebra.mapRingHom_comp
    (M := CompletedGroupAlgebraQuotientInClass G C U) g f).symm

/-- A finite coefficient ring gives finite \(C\)-indexed completed-group-algebra stages. -/
theorem finite_completedGroupAlgebraStageInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [Finite R] (U : CompletedGroupAlgebraIndexInClass G C) :
    Finite (CompletedGroupAlgebraStageInClass C R G U) := by
  classical
  let : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
    finite_completedGroupAlgebraQuotientInClass G C U
  let f :
      CompletedGroupAlgebraStageInClass C R G U →
        CompletedGroupAlgebraQuotientInClass G C U → R := fun x q => x.coeff q
  refine Finite.of_injective f ?_
  intro x y hxy
  ext q
  exact congrFun hxy q

/-- The transition map \(R[G/V] \to R[G/U]\) in the \(C\)-indexed completed-group-algebra tower. -/
def completedGroupAlgebraTransitionInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (R : Type u) (G : Type v) [CommRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    CompletedGroupAlgebraStageInClass C R G V →+*
      CompletedGroupAlgebraStageInClass C R G U :=
  MonoidAlgebra.mapDomainRingHom R
    (OpenNormalSubgroupInClass.map
      (C := C) (G := G) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)

/-- The transition map sends group-like basis elements by quotient projection. -/
@[simp]
theorem completedGroupAlgebraTransitionInClass_of
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (g : CompletedGroupAlgebraQuotientInClass G C V) :
    completedGroupAlgebraTransitionInClass C R G hUV (MonoidAlgebra.of R _ g) =
      MonoidAlgebra.single ((OpenNormalSubgroupInClass.map
        (C := C) (G := G) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) g) 1 := by
  classical
  change
    MonoidAlgebra.mapDomain
        (OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) g) 1
  exact MonoidAlgebra.mapDomain_single

/--
The \(C\)-indexed transition map between finite stages sends a singleton supported at a class of
the finer quotient to the singleton supported at its image in the coarser quotient, preserving
the coefficient.
-/
@[simp]
theorem completedGroupAlgebraTransitionInClass_single
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (q : CompletedGroupAlgebraQuotientInClass G C V) (r : R) :
    completedGroupAlgebraTransitionInClass C R G hUV (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) r := by
  classical
  change
    MonoidAlgebra.mapDomain
        (OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) r
  exact MonoidAlgebra.mapDomain_single

/-- The identity transition map in the \(C\)-indexed tower is the identity ring homomorphism. -/
@[simp]
theorem completedGroupAlgebraTransitionInClass_id
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C) :
    completedGroupAlgebraTransitionInClass C R G (le_rfl : U ≤ U) = RingHom.id _ := by
  rw [completedGroupAlgebraTransitionInClass, OpenNormalSubgroupInClass.map_id]
  exact MonoidAlgebra.mapDomainRingHom_id
    (R := R) (M := CompletedGroupAlgebraQuotientInClass G C U)

/-- Transition maps in the \(C\)-indexed tower compose as expected. -/
@[simp]
theorem completedGroupAlgebraTransitionInClass_comp
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V W : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) (hVW : V ≤ W) :
    (completedGroupAlgebraTransitionInClass C R G hUV).comp
        (completedGroupAlgebraTransitionInClass C R G hVW) =
      completedGroupAlgebraTransitionInClass C R G (hUV.trans hVW) := by
  unfold completedGroupAlgebraTransitionInClass
  exact
    (MonoidAlgebra.mapDomainRingHom_comp (R := R)
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual V) (V := OrderDual.ofDual W) hVW)).symm.trans
      (congrArg (MonoidAlgebra.mapDomainRingHom R)
        (OpenNormalSubgroupInClass.map_comp
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) (W := OrderDual.ofDual W)
          hUV hVW))

/-- \(C\)-indexed stage transitions commute with coefficient change. -/
@[simp]
theorem completedGroupAlgebraStageCoeffMapInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{v}) (S : Type w) [CommRing S] (f : R →+* S)
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U).comp
        (completedGroupAlgebraTransitionInClass C R G hUV) =
      (completedGroupAlgebraTransitionInClass C S G hUV).comp
        (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f V) := by
  exact MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
    (f := f)
    (g := OpenNormalSubgroupInClass.map
      (C := C) (G := G) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)

/--
Two coefficient changes and two \(C\)-indexed group-quotient transitions compose as the combined
change and combined transition.
-/
@[simp 900]
theorem completedGroupAlgebraStageCoeffMapInClass_transition_comp
    (C : ProCGroups.FiniteGroupClass.{v}) (S : Type w) (T : Type*) [CommRing S]
    [CommRing T] (f : R →+* S) (g : S →+* T)
    {U V W : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) (hVW : V ≤ W) :
    ((completedGroupAlgebraStageCoeffMapInClass (R := S) (G := G) C T g U).comp
        (completedGroupAlgebraTransitionInClass C S G hUV)).comp
        ((completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f V).comp
          (completedGroupAlgebraTransitionInClass C R G hVW)) =
      (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C T (g.comp f) U).comp
        (completedGroupAlgebraTransitionInClass C R G (hUV.trans hVW)) := by
  calc
    ((completedGroupAlgebraStageCoeffMapInClass (R := S) (G := G) C T g U).comp
        (completedGroupAlgebraTransitionInClass C S G hUV)).comp
        ((completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f V).comp
          (completedGroupAlgebraTransitionInClass C R G hVW))
      =
    (completedGroupAlgebraStageCoeffMapInClass (R := S) (G := G) C T g U).comp
      (((completedGroupAlgebraTransitionInClass C S G hUV).comp
        (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f V)).comp
        (completedGroupAlgebraTransitionInClass C R G hVW)) := by
          apply RingHom.ext
          intro x
          rfl
    _ =
    (completedGroupAlgebraStageCoeffMapInClass (R := S) (G := G) C T g U).comp
      (((completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U).comp
        (completedGroupAlgebraTransitionInClass C R G hUV)).comp
        (completedGroupAlgebraTransitionInClass C R G hVW)) := by
          rw [← completedGroupAlgebraStageCoeffMapInClass_compatible
            (R := R) (G := G) C S f hUV]
    _ =
    ((completedGroupAlgebraStageCoeffMapInClass (R := S) (G := G) C T g U).comp
        (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U)).comp
      ((completedGroupAlgebraTransitionInClass C R G hUV).comp
        (completedGroupAlgebraTransitionInClass C R G hVW)) := by
          apply RingHom.ext
          intro x
          rfl
    _ =
    (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C T (g.comp f) U).comp
      ((completedGroupAlgebraTransitionInClass C R G hUV).comp
        (completedGroupAlgebraTransitionInClass C R G hVW)) := by
          rw [completedGroupAlgebraStageCoeffMapInClass_comp]
    _ =
    (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C T (g.comp f) U).comp
      (completedGroupAlgebraTransitionInClass C R G (hUV.trans hVW)) := by
        rw [completedGroupAlgebraTransitionInClass_comp]

/-- Transition maps commute with scalar multiplication by coefficients. -/
theorem completedGroupAlgebraTransitionInClass_smul
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (r : R) (x : CompletedGroupAlgebraStageInClass C R G V) :
    completedGroupAlgebraTransitionInClass C R G hUV (r • x) =
      r • completedGroupAlgebraTransitionInClass C R G hUV x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  change
    MonoidAlgebra.mapDomain
        (OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (MonoidAlgebra.single 1 r) =
      MonoidAlgebra.single 1 r
  rw [MonoidAlgebra.mapDomain_single, map_one]

/-- Transition maps commute with the coefficient algebra maps. -/
theorem completedGroupAlgebraTransitionInClass_algebraMap
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) (r : R) :
    completedGroupAlgebraTransitionInClass C R G hUV
        (algebraMap R (CompletedGroupAlgebraStageInClass C R G V) r) =
      algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r := by
  change
    MonoidAlgebra.mapDomain
        (OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (MonoidAlgebra.single 1 r) =
      MonoidAlgebra.single 1 r
  rw [MonoidAlgebra.mapDomain_single, map_one]

/-- The quotient map from the abstract group algebra \(R[G]\) to one \(C\)-indexed finite stage. -/
def completedGroupAlgebraStageMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (R : Type u) (G : Type v) [CommRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    MonoidAlgebra R G →+* CompletedGroupAlgebraStageInClass C R G U :=
  MonoidAlgebra.mapDomainRingHom R
    (openNormalSubgroupInClassProj (C := C) (G := G) U)

/--
At a \(C\)-indexed stage \(U\), the quotient map sends the group-like element of \(g\) to the
singleton at the image of \(g\) in \(G/U\), with coefficient \(1\).
-/
@[simp]
theorem completedGroupAlgebraStageMapInClass_of
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (g : G) :
    completedGroupAlgebraStageMapInClass C R G U (MonoidAlgebra.of R G g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U g) 1 := by
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj (C := C) (G := G) U)
        (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single
        (openNormalSubgroupInClassProj (C := C) (G := G) U g) 1
  exact MonoidAlgebra.mapDomain_single

/--
At a \(C\)-indexed stage \(U\), the quotient map sends the singleton at \(g\) with coefficient
\(r\) to the singleton at the image of \(g\) in \(G/U\), with coefficient \(r\).
-/
theorem completedGroupAlgebraStageMapInClass_single
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (g : G) (r : R) :
    completedGroupAlgebraStageMapInClass C R G U (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U g) r := by
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj (C := C) (G := G) U)
        (MonoidAlgebra.single g r) =
      MonoidAlgebra.single
        (openNormalSubgroupInClassProj (C := C) (G := G) U g) r
  exact MonoidAlgebra.mapDomain_single

/-- The \(C\)-indexed quotient-stage map preserves scalar multiplication by elements of \(R\). -/
theorem completedGroupAlgebraStageMapInClass_smul
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (r : R) (x : MonoidAlgebra R G) :
    completedGroupAlgebraStageMapInClass C R G U (r • x) =
      r • completedGroupAlgebraStageMapInClass C R G U x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj (C := C) (G := G) U)
        (MonoidAlgebra.single 1 r) =
      MonoidAlgebra.single 1 r
  rw [MonoidAlgebra.mapDomain_single,
    (openNormalSubgroupInClassProj (C := C) (G := G) U).map_one]

/--
The \(C\)-indexed quotient-stage map commutes with the canonical embeddings of scalars from
\(R\).
-/
theorem completedGroupAlgebraStageMapInClass_algebraMap
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (r : R) :
    completedGroupAlgebraStageMapInClass C R G U (algebraMap R (MonoidAlgebra R G) r) =
      algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r := by
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj (C := C) (G := G) U)
        (MonoidAlgebra.single 1 r) =
      MonoidAlgebra.single 1 r
  rw [MonoidAlgebra.mapDomain_single,
    (openNormalSubgroupInClassProj (C := C) (G := G) U).map_one]

/-- The quotient map \(R[G]\to R[G/U]\) is surjective for every \(C\)-indexed stage \(U\). -/
theorem completedGroupAlgebraStageMapInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C) :
    Function.Surjective (completedGroupAlgebraStageMapInClass C R G U) := by
  classical
  intro x
  obtain ⟨y, hy⟩ :=
    Finsupp.mapDomain_surjective (M := R)
      (openNormalSubgroupInClassProj_surjective (C := C) (G := G) U) x.coeff
  refine ⟨MonoidAlgebra.ofCoeff y, ?_⟩
  apply MonoidAlgebra.coeff_injective
  exact hy

/--
The class-restricted completed group-algebra stage map is compatible with transition maps and
coordinate projections for the completed group algebra.
-/
@[simp]
theorem completedGroupAlgebraStageMapInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (completedGroupAlgebraTransitionInClass C R G hUV).comp
        (completedGroupAlgebraStageMapInClass C R G V) =
      completedGroupAlgebraStageMapInClass C R G U := by
  unfold completedGroupAlgebraTransitionInClass completedGroupAlgebraStageMapInClass
  have hproj :
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV).comp
          (openNormalSubgroupInClassProj (C := C) (G := G) V) =
        openNormalSubgroupInClassProj (C := C) (G := G) U := by
    ext g
    exact congrFun
      (openNormalSubgroupInClassProj_compatible
        (C := C) (G := G) U V hUV) g
  exact
    (MonoidAlgebra.mapDomainRingHom_comp (R := R)
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
      (openNormalSubgroupInClassProj (C := C) (G := G) V)).symm.trans
      (congrArg (MonoidAlgebra.mapDomainRingHom R) hproj)

variable [TopologicalSpace R] [IsTopologicalRing R]

end InClass

end

end CompletedGroupAlgebra
