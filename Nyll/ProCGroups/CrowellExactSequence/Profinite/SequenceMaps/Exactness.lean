/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CrowellExactSequence.Basic
import Nyll.ProCGroups.CrowellExactSequence.Profinite.SequenceMaps.Basic
import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.ClosedGeneratedCoordinates.Topology
import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.TailExactness

/-!
# Exactness criteria for profinite Crowell sequence maps

This file identifies the completed map with the boundary expressed in closed-generator
coordinates and transfers exactness between finite-family, completed, and separated sequences.
It gives topological-generation and basis criteria and computes the maps on kernel elements.
-/

namespace CrowellExactSequence

noncomputable section

open scoped BigOperators
open FoxDifferential

universe u v w

variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

section ClosedGeneratedCoordinates

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
variable (C : ProCGroups.FiniteGroupClass.{u})
variable (psi : ContinuousMonoidHom G H)
variable {X : Type u} [Fintype X] [DecidableEq X]
variable (family : X → G)
variable
  (hfree :
    ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X G family)
variable
  (htarget :
    ProCGroups.ProC.HasOpenNormalBasisInClass C
      (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (C := C) (fun i : X => psi (family i)) : Subgroup
          (ZCCompletedFoxSemidirect C X H)))
variable
  (hφconv :
    ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
      (G :=
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (C := C) (fun i : X => psi (family i)) : Subgroup
            (ZCCompletedFoxSemidirect C X H)))
      (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
        (C := C) (fun i : X => psi (family i))))


/--
On the genuine \(A_{\psi}(C)\), the Crowell boundary is obtained by first reading the
closed-generated Fox coordinates and then applying the completed Fox boundary.
-/
theorem presentedCompletedToZC_eq_boundary_comp_closedGenCoords
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : X => psi (family i)))
    (hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C psi =
      (freeProCZCCompletedFoxBoundary C
        (fun i : X => psi (family i))).comp
        (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) C psi family hfree htarget hφconv
          hH hφHconv hφHgen) := by
  apply
    crossedDifferentialModuleHom_ext
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
  intro g
  change
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C psi
        (zcUniversalDifferential C psi.toMonoidHom g) =
      ((freeProCZCCompletedFoxBoundary C
        (fun i : X => psi (family i))).comp
        (closedGeneratedDerivativeCoordinatesLinearMapProCInteger
          (G := G) (H := H) C psi family hfree htarget hφconv
          hH hφHconv hφHgen))
        (zcUniversalDifferential C psi.toMonoidHom g)
  rw [presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_d,
    LinearMap.comp_apply,
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal]
  have hright :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (C := C) hfree (fun i : X => psi (family i)) htarget hφconv =
        psi.toMonoidHom :=
    freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
      (C := C) X H hfree hH (fun i : X => psi (family i)) htarget hφconv
      hφHconv hφHgen psi (by intro i; rfl)
  let delta : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)
      (ZCFreeFoxCoordinates C (X := X) (H := H)) :=
    { toFun := fun g =>
        freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
          (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g
      map_mul' := by
        intro a b
        rw [← hright]
        exact
          ScalarCrossedHom.map_mul
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv)
            a b }
  exact
    (freeProCZCBoundary_of_topologicalGeneration
      C hfree.generates_range psi.toMonoidHom
      delta
      (by
        change Continuous
          (fun g : G =>
            freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv g)
        exact
          continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) X H hfree (fun i : X => psi (family i)) htarget hφconv)
      psi.continuous_toFun
      (by
        intro i
        change
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : X => psi (family i)) htarget hφconv
              (family i) =
            Pi.single i (1 : ZCCompletedGroupAlgebra C H)
        exact
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_generator
            (C := C) hfree (fun i : X => psi (family i)) htarget hφconv i)
      g).symm

end ClosedGeneratedCoordinates

variable (C : ProCGroups.FiniteGroupClass.{u})

omit [IsTopologicalGroup G] in
/--
The displayed Crowell map after the family map is the finite Blanchfield--Lyndon map with
boundary generators \(\psi(\mathrm{family}\ i)-1\).
-/
theorem presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G) :
    (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C psi).comp
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family) =
      blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : X =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := G) (H := H) C psi (family i)) := by
  classical
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, presentedCompletedDifferentialFamilyMapProCInteger,
    blanchfieldLyndonFiniteFamilyMap_apply, blanchfieldLyndonFiniteFamilyMap_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_d]

omit [IsTopologicalGroup G] in
/--
The separated displayed Crowell map after the separated family map is the finite
Blanchfield--Lyndon map with boundary generators \(\psi(\mathrm{family}\ i)-1\).
-/
theorem presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G) :
    (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi).comp
        (presentedSeparatedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family) =
      blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : X =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := G) (H := H) C psi (family i)) := by
  classical
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, presentedSeparatedDifferentialFamilyMapProCInteger,
    blanchfieldLyndonFiniteFamilyMap_apply, blanchfieldLyndonFiniteFamilyMap_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_d]


omit [IsTopologicalGroup G] in
/--
The finite Blanchfield--Lyndon boundary attached to the displayed family is exactly the
source-shaped completed Fox boundary for the abstract free group on that family. This removes
one layer from the remaining density statement: a BL-coordinate cycle is the same as a vector
killed by the completed Fox boundary \(zcFreeGroupFoxBoundary C (FreeGroup.lift (fun i \mapsto
psi (family i)))\).
-/
theorem finiteBLMap_boundaryZC_eq_zcFreeGroupFoxBoundary
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G) :
    blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : X =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := G) (H := H) C psi (family i)) =
      FoxDifferential.zcFreeGroupFoxBoundary
        C (FreeGroup.lift (fun i : X => psi (family i))) := by
  classical
  apply LinearMap.ext
  intro v
  change
    (∑ x : X, v x *
      (zcGroupLike C H (psi (family x)) - 1)) =
      ∑ x : X, v x *
        (zcGroupLike C H
          (FreeGroup.lift (fun i : X => psi (family i)) (FreeGroup.of x)) - 1)
  simp only [FreeGroup.lift_apply_of]

omit [IsTopologicalGroup G] in
/--
If the pushed-forward finite family topologically generates \(H\), the finite
Blanchfield--Lyndon map is used at the completed group algebra.
-/
theorem exact_blanchfieldLyndonFiniteFamilyMap_boundary_family_of_topologicallyGenerates
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G)
    (hgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    Function.Exact
      (blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : X =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := G) (H := H) C psi (family i)))
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H -> ZCCoeff C) := by
  classical
  have hfoxExact :
      Function.Exact
        (FoxDifferential.foxBoundaryMap
          (fun i : X => zcGroupLike C H (psi (family i)) - 1) :
          (X → ZCCompletedGroupAlgebra C H) →
            ZCCompletedGroupAlgebra C H)
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H → ZCCoeff C) :=
    FoxDifferential.exact_foxBoundaryMap_zcGroupLike_sub_one_of_topologicallyGenerates
      (C := C) (hForm := hForm)
      (φ := fun i : X => psi (family i)) hgen
  have hmap :
      blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra C H)
          (fun i : X =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := G) (H := H) C psi (family i)) =
        FoxDifferential.foxBoundaryMap
          (fun i : X => zcGroupLike C H (psi (family i)) - 1) := by
    rw [finiteBLMap_boundaryZC_eq_zcFreeGroupFoxBoundary
      (G := G) (H := H) C psi family]
    apply LinearMap.ext
    intro v
    change
      (∑ x : X, v x *
        (zcGroupLike C H
          (FreeGroup.lift (fun i : X => psi (family i)) (FreeGroup.of x)) - 1)) =
        ∑ x : X, v x * (zcGroupLike C H (psi (family x)) - 1)
    simp only [FreeGroup.lift_apply_of]
  rw [hmap]
  exact hfoxExact

omit [IsTopologicalGroup G] in
/--
Exactness of the finite Blanchfield--Lyndon map implies exactness of the displayed Crowell map;
no coordinate basis hypothesis is needed in this direction.
-/
theorem exact_presentedCompletedToZC_of_blanchfieldLyndonFiniteFamilyMap_boundary_family
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G)
    (hbl :
      Function.Exact
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra C H)
          (fun i : X =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := G) (H := H) C psi (family i)))
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H -> ZCCoeff C)) :
    Function.Exact
      (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi :
        ZCCompletedDifferentialModule C psi.toMonoidHom -> ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H -> ZCCoeff C) := by
  classical
  let familyMap :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let delta :=
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
      (G := G) (H := H) C psi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : X =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := G) (H := H) C psi (family i))
  have hcomp : delta.comp familyMap = blDelta :=
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
      (G := G) (H := H) C psi family
  have hdelta_family : ∀ x, delta (familyMap x) = blDelta x := by
    intro x
    have hx := congrArg (fun f => f x) hcomp
    change delta (familyMap x) = blDelta x at hx
    exact hx
  intro z
  constructor
  · intro hz
    rcases (hbl z).1 hz with ⟨x, hx⟩
    exact ⟨familyMap x, (hdelta_family x).trans hx⟩
  · rintro ⟨m, rfl⟩
    have hmem :
        delta m ∈ zcCompletedGroupAlgebraAugmentationIdeal C H := by
      have hstd :
          delta m ∈ zcCompletedGroupAlgebraStandardAugmentationIdeal C H := by
        simpa [delta, presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger] using
          zcToCompletedGroupAlgebra_mem_standardAugmentationIdeal
            C H psi.toMonoidHom m
      exact zcCompletedGroupAlgebraStandardAugmentationIdeal_le_augmentationIdeal C H hstd
    exact (mem_zcCompletedGroupAlgebraAugmentationIdeal_iff
      (C := C) (H := H) (x := delta m)).1 hmem

omit [IsTopologicalGroup G] in
/--
If the pushed-forward finite family topologically generates \(H\), then the displayed Crowell
map is used at the completed group algebra.
-/
theorem exact_presentedCompletedToZC_of_boundary_family_topologicallyGenerates
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Finite X] (family : X -> G)
    (hgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    Function.Exact
      (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi :
        ZCCompletedDifferentialModule C psi.toMonoidHom -> ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H -> ZCCoeff C) := by
  classical
  let : Fintype X := Fintype.ofFinite X
  exact
    exact_presentedCompletedToZC_of_blanchfieldLyndonFiniteFamilyMap_boundary_family
      (G := G) (H := H) C psi family
      (exact_blanchfieldLyndonFiniteFamilyMap_boundary_family_of_topologicallyGenerates
        (G := G) (H := H) C hForm psi family hgen)

omit [IsTopologicalGroup G] in
/--
Exactness of the finite Blanchfield--Lyndon map implies exactness of the separated displayed
Crowell map at \(\mathbb{Z}_C\llbracket H\rrbracket\).
-/
theorem exact_presentedSepToZC_of_blanchfieldLyndonFiniteFamilyMap_boundary_family
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G)
    (hbl :
      Function.Exact
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra C H)
          (fun i : X =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := G) (H := H) C psi (family i)))
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H -> ZCCoeff C)) :
    Function.Exact
      (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi :
        ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom ->
          ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H -> ZCCoeff C) := by
  classical
  let familyMap :=
    presentedSeparatedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let delta :=
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
      (G := G) (H := H) C hC psi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : X =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := G) (H := H) C psi (family i))
  have hcomp : delta.comp familyMap = blDelta :=
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
      (G := G) (H := H) C hC psi family
  have hdelta_family : ∀ x, delta (familyMap x) = blDelta x := by
    intro x
    have hx := congrArg (fun f => f x) hcomp
    change delta (familyMap x) = blDelta x at hx
    exact hx
  have hcompleted :
      Function.Exact
        (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
          (G := G) (H := H) C psi :
          ZCCompletedDifferentialModule C psi.toMonoidHom -> ZCCompletedGroupAlgebra C H)
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H -> ZCCoeff C) :=
    exact_presentedCompletedToZC_of_blanchfieldLyndonFiniteFamilyMap_boundary_family
      (G := G) (H := H) C psi family hbl
  have htoSep_surj :
      Function.Surjective (zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom) := by
    intro a
    refine Submodule.Quotient.induction_on
      (p := zcCompletedDifferentialRelationFiniteClosedSubmodule C psi.toMonoidHom)
      (C := fun a =>
        ∃ b : ZCCompletedDifferentialModule C psi.toMonoidHom,
          zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom b = a)
      a ?_
    intro x
    refine ⟨(crossedDifferentialRelationSubmodule
      (zcCompletedGroupAlgebraScalar C psi.toMonoidHom)).mkQ x, ?_⟩
    rfl
  intro z
  constructor
  · intro hz
    rcases (hbl z).1 hz with ⟨x, hx⟩
    exact ⟨familyMap x, (hdelta_family x).trans hx⟩
  · rintro ⟨m, rfl⟩
    rcases htoSep_surj m with ⟨b, hb⟩
    have hdelta_lift :
        delta m =
          presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
            (G := G) (H := H) C psi b := by
      rw [← hb]
      have hcomp_toSep :=
        congrArg (fun f => f b)
          (presentedSepToZC_comp_toSep
            (G := G) (H := H) C hC psi)
      change
        delta (zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom b) =
          presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
            (G := G) (H := H) C psi b at hcomp_toSep
      exact hcomp_toSep
    rw [hdelta_lift]
    exact
      (hcompleted
        (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
          (G := G) (H := H) C psi b)).2 ⟨b, rfl⟩

omit [IsTopologicalGroup G] in
/--
If the pushed-forward finite family topologically generates \(H\), then the separated displayed
Crowell map is used at the completed group algebra.
-/
theorem exact_presentedSepToZC_of_boundary_family_topologicallyGenerates
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Finite X] (family : X -> G)
    (hgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : X => psi (family i)))) :
    Function.Exact
      (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi :
        ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom ->
          ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H -> ZCCoeff C) := by
  classical
  let : Fintype X := Fintype.ofFinite X
  exact
    exact_presentedSepToZC_of_blanchfieldLyndonFiniteFamilyMap_boundary_family
      (G := G) (H := H) C hC psi family
      (exact_blanchfieldLyndonFiniteFamilyMap_boundary_family_of_topologicallyGenerates
        (G := G) (H := H) C hForm psi family hgen)

omit [IsTopologicalGroup G] in
/--
Exactness of the displayed Crowell map implies exactness of the finite Blanchfield--Lyndon map
as soon as the chosen family map is surjective. Full basis/injectivity is not needed for this
implication.
-/
theorem exact_finiteBLMap_boundary_of_presentedToZC_of_familyMap_surj
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (psi : ContinuousMonoidHom G H)
    {X : Type v} [Fintype X] (family : X -> G)
    (hbasis_A_surj :
      Function.Surjective
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := G) (H := H) C psi family))
    (hexact_CompletedGroupAlgebra :
      Function.Exact
        (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi :
          ZCCompletedDifferentialModule C psi.toMonoidHom -> ZCCompletedGroupAlgebra C H)
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H -> ZCCoeff C)) :
    Function.Exact
      (blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : X =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := G) (H := H) C psi (family i)))
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H -> ZCCoeff C) := by
  classical
  let familyMap :=
    presentedCompletedDifferentialFamilyMapProCInteger
      (G := G) (H := H) C psi family
  let delta :=
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
      (G := G) (H := H) C psi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : X =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := G) (H := H) C psi (family i))
  have hcomp : delta.comp familyMap = blDelta :=
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
      (G := G) (H := H) C psi family
  have hdelta_family : ∀ x, delta (familyMap x) = blDelta x := by
    intro x
    have hx := congrArg (fun f => f x) hcomp
    change delta (familyMap x) = blDelta x at hx
    exact hx
  intro z
  constructor
  · intro hz
    rcases (hexact_CompletedGroupAlgebra z).1 hz with ⟨m, hm⟩
    rcases hbasis_A_surj m with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    calc
      blDelta x = delta (familyMap x) := (hdelta_family x).symm
      _ = delta m := by rw [hx]
      _ = z := hm
  · rintro ⟨x, rfl⟩
    exact (hexact_CompletedGroupAlgebra (blDelta x)).2 ⟨familyMap x, hdelta_family x⟩

omit [IsTopologicalGroup G] in
/--
A basis family identifies exactness of the displayed Crowell map with exactness of the finite
Blanchfield--Lyndon map obtained by evaluating the displayed boundary on that family.
-/
theorem exact_finiteBLMap_boundary_iff_presentedToZC_of_family_basis
    {C}
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    {psi : ContinuousMonoidHom G H}
    {X : Type v} [Fintype X] (family : X -> G)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := G) (H := H) C psi family) :
    Function.Exact
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra C H)
          (fun i : X =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := G) (H := H) C psi (family i)))
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H -> ZCCoeff C) <->
      Function.Exact
        (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi :
          ZCCompletedDifferentialModule C psi.toMonoidHom -> ZCCompletedGroupAlgebra C H)
        (zcCompletedGroupAlgebraAugmentation C H :
          ZCCompletedGroupAlgebra C H -> ZCCoeff C) := by
  constructor
  · exact
      exact_presentedCompletedToZC_of_blanchfieldLyndonFiniteFamilyMap_boundary_family
        (G := G) (H := H) C psi family
  · exact
      exact_finiteBLMap_boundary_of_presentedToZC_of_familyMap_surj
        (G := G) (H := H) C psi family hbasis_A.2

omit [IsTopologicalGroup G] in
/-- If \(g \in \ker \psi\), the displayed Crowell map sends \(dg\) to zero. -/
@[simp]
theorem presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_d_of_mem_ker
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    (n : psi.toMonoidHom.ker) :
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi
        (zcUniversalDifferential C psi.toMonoidHom n.1) =
      0 := by
  rw [presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_d]
  exact zcCompletedGroupAlgebraBoundary_eq_zero_of_mem_ker
    (C := C) (H := H) psi.toMonoidHom n.2

omit [IsTopologicalGroup G] in
/--
If \(g \in \ker \psi\), the separated Crowell boundary sends the separated differential \(dg\)
to zero.
-/
@[simp]
theorem presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_d_of_mem_ker
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (psi : ContinuousMonoidHom G H) (n : psi.toMonoidHom.ker) :
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := G) (H := H) C hC psi
        (zcSeparatedUniversalDifferential C psi.toMonoidHom n.1) =
      0 := by
  rw [presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_d]
  exact zcCompletedGroupAlgebraBoundary_eq_zero_of_mem_ker
    (C := C) (H := H) psi.toMonoidHom n.2

end

end CrowellExactSequence
