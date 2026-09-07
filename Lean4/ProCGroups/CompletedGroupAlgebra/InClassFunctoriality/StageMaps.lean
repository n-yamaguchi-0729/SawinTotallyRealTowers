import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.CanonicalMaps
import ProCGroups.CompletedGroupAlgebra.InClassFunctoriality.ComapIndex

set_option autoImplicit false

/-!
# Functorial maps at in-class finite stages

This file constructs the finite-stage group-algebra map induced by a continuous group
homomorphism. It proves formulas on basis elements and scalars and compatibility with coefficient
change, transitions, and the completed map.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The \(C\)-indexed finite-stage map \(R[G/\varphi^{-1}(V)]\to R[H/V]\) is induced by a continuous
homomorphism \(\varphi : G \to H\).
-/
def completedGroupAlgebraFunctorialStageMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (R : Type u) [CommRing R] (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndexInClass H C) :
    CompletedGroupAlgebraStageInClass C R G
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) →+*
      CompletedGroupAlgebraStageInClass C R H V :=
  MonoidAlgebra.mapDomainRingHom R
    (completedGroupAlgebraComapQuotientMapInClass (G := G) (H := H) C hHer φ hφ V)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- A surjective group homomorphism induces a surjective finite-stage group-algebra map. -/
theorem completedGroupAlgebraFunctorialStageMapInClass_surjective_of_surjective
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (hφsurj : Function.Surjective φ)
    (V : CompletedGroupAlgebraIndexInClass H C) :
    Function.Surjective
      (completedGroupAlgebraFunctorialStageMapInClass
        (G := G) (H := H) C hHer (R := R) φ hφ V) := by
  intro x
  obtain ⟨y, hy⟩ :=
    Finsupp.mapDomain_surjective (M := R)
      (completedGroupAlgebraComapQuotientMapInClass_surjective_of_surjective
        (G := G) (H := H) C hHer φ hφ hφsurj V) x.coeff
  refine ⟨MonoidAlgebra.ofCoeff y, ?_⟩
  apply MonoidAlgebra.coeff_injective
  exact hy

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The functorial finite-stage map sends singleton coefficients to singleton coefficients. -/
@[simp]
theorem completedGroupAlgebraFunctorialStageMapInClass_single
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (V : CompletedGroupAlgebraIndexInClass H C)
    (q : CompletedGroupAlgebraQuotientInClass G C
      (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)) (r : R) :
    completedGroupAlgebraFunctorialStageMapInClass
        (G := G) (H := H) C hHer (R := R) φ hφ V (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        (completedGroupAlgebraComapQuotientMapInClass (G := G) (H := H)
          C hHer φ hφ V q) r := by
  change
    MonoidAlgebra.mapDomain
        (completedGroupAlgebraComapQuotientMapInClass
          (G := G) (H := H) C hHer φ hφ V)
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        (completedGroupAlgebraComapQuotientMapInClass
          (G := G) (H := H) C hHer φ hφ V q) r
  exact MonoidAlgebra.mapDomain_single

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The functorial finite-stage map preserves coefficient algebra-map elements. -/
theorem completedGroupAlgebraFunctorialStageMapInClass_algebraMap
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (V : CompletedGroupAlgebraIndexInClass H C) (r : R) :
    completedGroupAlgebraFunctorialStageMapInClass
        (G := G) (H := H) C hHer (R := R) φ hφ V
        (algebraMap R
          (CompletedGroupAlgebraStageInClass C R G
            (completedGroupAlgebraComapIndexInClass
              (G := G) (H := H) C hHer φ hφ V)) r) =
      algebraMap R (CompletedGroupAlgebraStageInClass C R H V) r := by
  change
    MonoidAlgebra.mapDomain
        (completedGroupAlgebraComapQuotientMapInClass
          (G := G) (H := H) C hHer φ hφ V)
        (MonoidAlgebra.single 1 r) =
      MonoidAlgebra.single 1 r
  rw [MonoidAlgebra.mapDomain_single,
    (completedGroupAlgebraComapQuotientMapInClass
      (G := G) (H := H) C hHer φ hφ V).map_one]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Functorial finite-stage maps commute with coefficient change. -/
@[simp]
theorem completedGroupAlgebraStageCoeffMapInClass_comp_functorialStageMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (S : Type w) [CommRing S] (f : R →+* S)
    (φ : G →* H) (hφ : Continuous φ) (V : CompletedGroupAlgebraIndexInClass H C) :
    (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := H) C S f V).comp
        (completedGroupAlgebraFunctorialStageMapInClass
          (G := G) (H := H) C hHer (R := R) φ hφ V) =
      (completedGroupAlgebraFunctorialStageMapInClass
          (G := G) (H := H) C hHer (R := S) φ hφ V).comp
        (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f
          (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)) := by
  exact MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
    (f := f)
    (g := completedGroupAlgebraComapQuotientMapInClass
      (G := G) (H := H) C hHer φ hφ V)

/-- The functorial finite-stage group-algebra map is continuous for the finite-stage topologies. -/
theorem continuous_completedGroupAlgebraFunctorialStageMapInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (V : CompletedGroupAlgebraIndexInClass H C) :
    letI : TopologicalSpace
        (CompletedGroupAlgebraStageInClass C R G
          (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)) :=
      (completedGroupAlgebraSystemInClass C R G).topologicalSpace
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)
    letI : TopologicalSpace (CompletedGroupAlgebraStageInClass C R H V) :=
      (completedGroupAlgebraSystemInClass C R H).topologicalSpace V
    Continuous (completedGroupAlgebraFunctorialStageMapInClass
      (G := G) (H := H) C hHer (R := R) φ hφ V) := by
  let : Finite (CompletedGroupAlgebraQuotientInClass G C
      (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)) :=
    finite_completedGroupAlgebraQuotientInClass G C
      (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)
  let : Finite (CompletedGroupAlgebraQuotientInClass H C V) :=
    finite_completedGroupAlgebraQuotientInClass H C V
  let : TopologicalSpace
      (CompletedGroupAlgebraStageInClass C R G
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)) :=
    (completedGroupAlgebraSystemInClass C R G).topologicalSpace
      (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)
  let : TopologicalSpace (CompletedGroupAlgebraStageInClass C R H V) :=
    (completedGroupAlgebraSystemInClass C R H).topologicalSpace V
  exact finiteGroupAlgebra_mapDomainRingHom_continuous R
    (CompletedGroupAlgebraQuotientInClass G C
      (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V))
    (CompletedGroupAlgebraQuotientInClass H C V)
    (completedGroupAlgebraComapQuotientMapInClass (G := G) (H := H) C hHer φ hφ V)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Functorial finite-stage maps commute with transition maps. -/
@[simp]
theorem completedGroupAlgebraFunctorialStageMapInClass_transition
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ)
    {V W : CompletedGroupAlgebraIndexInClass H C} (hVW : V ≤ W) :
    (completedGroupAlgebraTransitionInClass C R H hVW).comp
        (completedGroupAlgebraFunctorialStageMapInClass
          (G := G) (H := H) C hHer (R := R) φ hφ W) =
      (completedGroupAlgebraFunctorialStageMapInClass
          (G := G) (H := H) C hHer (R := R) φ hφ V).comp
        (completedGroupAlgebraTransitionInClass C R G
          (completedGroupAlgebraComapIndexInClass_mono
            (G := G) (H := H) C hHer φ hφ hVW)) := by
  unfold completedGroupAlgebraTransitionInClass
    completedGroupAlgebraFunctorialStageMapInClass
  exact
    (MonoidAlgebra.mapDomainRingHom_comp (R := R)
      (OpenNormalSubgroupInClass.map
        (C := C) (G := H)
        (U := OrderDual.ofDual V) (V := OrderDual.ofDual W) hVW)
      (completedGroupAlgebraComapQuotientMapInClass
        (G := G) (H := H) C hHer φ hφ W)).symm.trans
      ((congrArg (MonoidAlgebra.mapDomainRingHom R)
        (completedGroupAlgebraComapQuotientMapInClass_compatible
          (G := G) (H := H) C hHer φ hφ hVW)).trans
        (MonoidAlgebra.mapDomainRingHom_comp (R := R)
          (completedGroupAlgebraComapQuotientMapInClass
            (G := G) (H := H) C hHer φ hφ V)
          (OpenNormalSubgroupInClass.map
            (C := C) (G := G)
            (U := OrderDual.ofDual
              (completedGroupAlgebraComapIndexInClass
                (G := G) (H := H) C hHer φ hφ V))
            (V := OrderDual.ofDual
              (completedGroupAlgebraComapIndexInClass
                (G := G) (H := H) C hHer φ hφ W))
            (completedGroupAlgebraComapIndexInClass_mono
              (G := G) (H := H) C hHer φ hφ hVW))))

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Functorial finite-stage maps commute with a group transition followed by coefficient change. -/
theorem completedGAStageCoeffMapInClass_comp_transition_comp_functorialStageMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (S : Type w) [CommRing S] (f : R →+* S)
    (φ : G →* H) (hφ : Continuous φ)
    {V W : CompletedGroupAlgebraIndexInClass H C} (hVW : V ≤ W) :
    ((completedGroupAlgebraStageCoeffMapInClass (R := R) (G := H) C S f V).comp
        (completedGroupAlgebraTransitionInClass C R H hVW)).comp
        (completedGroupAlgebraFunctorialStageMapInClass
          (G := G) (H := H) C hHer (R := R) φ hφ W) =
      (completedGroupAlgebraFunctorialStageMapInClass
          (G := G) (H := H) C hHer (R := S) φ hφ V).comp
        ((completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f
          (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)).comp
          (completedGroupAlgebraTransitionInClass C R G
            (completedGroupAlgebraComapIndexInClass_mono
              (G := G) (H := H) C hHer φ hφ hVW))) := by
  rw [RingHom.comp_assoc]
  rw [completedGroupAlgebraFunctorialStageMapInClass_transition]
  rw [← RingHom.comp_assoc]
  rw [completedGroupAlgebraStageCoeffMapInClass_comp_functorialStageMapInClass]
  rw [RingHom.comp_assoc]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The functorial finite-stage map agrees with the stage map after passing to the comap quotient.
-/
@[simp]
theorem completedGroupAlgebraFunctorialStageMapInClass_comp_stageMap
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (V : CompletedGroupAlgebraIndexInClass H C) :
    (completedGroupAlgebraFunctorialStageMapInClass
        (G := G) (H := H) C hHer (R := R) φ hφ V).comp
        (completedGroupAlgebraStageMapInClass C R G
          (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V)) =
      (completedGroupAlgebraStageMapInClass C R H V).comp
        (MonoidAlgebra.mapDomainRingHom R φ) := by
  unfold completedGroupAlgebraFunctorialStageMapInClass
    completedGroupAlgebraStageMapInClass
  have hmap :
      (completedGroupAlgebraComapQuotientMapInClass
          (G := G) (H := H) C hHer φ hφ V).comp
          (openNormalSubgroupInClassProj
            (C := C) (G := G)
            (completedGroupAlgebraComapIndexInClass
              (G := G) (H := H) C hHer φ hφ V)) =
        (openNormalSubgroupInClassProj (C := C) (G := H) V).comp φ := by
    ext g
    exact completedGroupAlgebraComapQuotientMapInClass_mk
      (G := G) (H := H) C hHer φ hφ V g
  exact
    (MonoidAlgebra.mapDomainRingHom_comp (R := R)
      (completedGroupAlgebraComapQuotientMapInClass
        (G := G) (H := H) C hHer φ hφ V)
      (openNormalSubgroupInClassProj
        (C := C) (G := G)
        (completedGroupAlgebraComapIndexInClass
          (G := G) (H := H) C hHer φ hφ V))).symm.trans
      ((congrArg (MonoidAlgebra.mapDomainRingHom R) hmap).trans
        (MonoidAlgebra.mapDomainRingHom_comp (R := R)
          (openNormalSubgroupInClassProj (C := C) (G := H) V) φ))

end

end CompletedGroupAlgebra
