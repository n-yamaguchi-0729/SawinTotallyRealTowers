/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CrowellExactSequence.Profinite.ContinuousMagnus.Injectivity
import Nyll.ProCGroups.CrowellExactSequence.Profinite.Exactness
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.FundamentalFormula

/-!
# Free pro-C Crowell exactness

For a free pro-\(C\) source, this file combines continuous Magnus injectivity, the completed
boundary calculation, and bifiltered finite-stage exactness. The resulting theorems assemble the
presented and separated Crowell exact sequences under a surjective presentation map.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential
open ProCGroups.ProC

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {C : ProCGroups.FiniteGroupClass.{u}}

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]

/--
For surjective \(\psi\), the presented Crowell group-algebra sequence over the pro-\(C\)
integers is exact.
-/
theorem freeProC_presentedCrowellGroupAlgebraExactProCInteger_of_psi_surjective
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    Function.Exact
      (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
        (G := sourceData.carrier) (H := H) C psi)
      (zcCompletedGroupAlgebraAugmentation C H) := by
  let family : ULift.{u} (Fin r) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis
  have htargetGen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : ULift.{u} (Fin r) => psi (family i))) := by
    simpa [family] using
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (C := C) sourceData hbasis psi hpsi
  exact
    exact_presentedCompletedToZC_of_boundary_family_topologicallyGenerates
      (G := sourceData.carrier) (H := H) C
      hForm psi family htargetGen

/--
For surjective \(\psi\), the separated presented Crowell group-algebra sequence over the
pro-\(C\) integers is exact.
-/
theorem freeProC_presentedSeparatedCrowellGroupAlgebraExactProCInteger_of_psi_surjective
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    Function.Exact
      (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := sourceData.carrier) (H := H) C
        hC.hereditary psi)
      (zcCompletedGroupAlgebraAugmentation C H) := by
  let family : ULift.{u} (Fin r) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis
  have htargetGen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : ULift.{u} (Fin r) => psi (family i))) := by
    simpa [family] using
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (C := C) sourceData hbasis psi hpsi
  exact
    exact_presentedSepToZC_of_boundary_family_topologicallyGenerates
      (G := sourceData.carrier) (H := H) C
      hC.hereditary
      (hC.melnikovFormation.formation) psi family htargetGen

/--
The continuous Magnus hypothesis makes the separated pro-\(C\) kernel-abelianization boundary
injective.
-/
theorem freeProC_profKerAbBoundaryAddZCSep_inj_of_continuousMagnus
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    [T1Space
      (ZCFreeFoxCoordinates C
        (X := ULift.{u} (Fin r)) (H := H))] :
    Function.Injective
      (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
        (G := sourceData.carrier) (H := H) C psi) := by
  apply
    profKerAbBoundaryAddZCSep_inj_of_kernel_le_closedCommutator
      (G := sourceData.carrier) (H := H) C psi
  intro n hnsep
  let htarget :=
    freeProCClosedGeneratedTarget_proC_of_surjective
      (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi
  apply
    freeProC_closedGeneratedFoxVector_kernel_le_closedCommutator
      (H := H) (C := C) hC sourceData hbasis psi hpsi htarget n
  have hcoord_zero :
      freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
          (H := H) (C := C) sourceData hbasis psi htarget n.1 = 0 := by
    have happly :=
      congrArg
        (freeProCChosenULift_sepCoordinateMap
          (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi) hnsep
    rw [freeProCChosenULift_sepCoordinateMap_universal] at happly
    calc
      freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
          (H := H) (C := C) sourceData hbasis psi htarget n.1 =
          freeProCChosenULift_sepCoordinateMap
            (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi 0 := by
        simpa [freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger,
          htarget] using happly
      _ = 0 :=
        (freeProCChosenULift_sepCoordinateMap
          (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi).map_zero
  exact hcoord_zero

omit [C.ContainsTrivialQuotients] in
/--
Under closed generation and surjectivity of \(\psi\), the completed boundary kills the
topological commutator subgroup.
-/
theorem freeProC_completedBoundaryKillsTopCommZC_of_closedGen_and_psi_surj
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (htarget :
      HasOpenNormalBasisInClass C
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (C := C)
          (fun i : ULift.{u} (Fin r) =>
            psi (freeProCChosenULiftFamilyOfBasisCard
              (C := C) sourceData hbasis i)) : Subgroup
            (ZCCompletedFoxSemidirect
              C (ULift.{u} (Fin r)) H)))
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := sourceData.carrier) (H := H) C psi
        (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis)) :
    CompletedBoundaryKillsTopologicalCommutatorProCInteger
      (G := sourceData.carrier) (H := H) C psi := by
  let family : ULift.{u} (Fin r) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis
  let hfree :=
    freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis
  let hφconv :=
    freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
      (C := C) (fun i : ULift.{u} (Fin r) => psi (family i))
  have hH : HasOpenNormalBasisInClass C H :=
    HasOpenNormalBasisInClass.of_surjective
      hForm
      sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass psi hpsi
  have hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : ULift.{u} (Fin r) => psi (family i)) := by
    simpa [family] using
      freeProCChosenULiftFamilyOfBasisCard_image_convergesToOneAlongOpenSubgroups
        (C := C) sourceData hbasis psi.toMonoidHom
  have hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : ULift.{u} (Fin r) => psi (family i))) := by
    simpa [family] using
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (C := C) sourceData hbasis psi hpsi
  have hleft_graph_eq :
      ∀ g : sourceData.carrier,
        freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree (fun i : ULift.{u} (Fin r) => psi (family i))
            htarget hφconv g =
          presentedCompletedDifferentialFamilyCoordinatesProCInteger
            (G := sourceData.carrier) (H := H) C psi family hbasis_A
            (zcUniversalDifferential C psi.toMonoidHom g) := by
    exact
      freeProCZCCompletedFoxDerivativeVectorViaClosedGen_eq_presentedCoordinates_zcUnivDiff
        (G := sourceData.carrier) (H := H) C psi family hbasis_A hfree hH htarget hφconv
        hφHconv hφHgen
  exact
    completedBoundaryKillsTopCommZC_of_closedGen_leftGraph
      (G := sourceData.carrier) (H := H) C psi family hbasis_A hfree htarget hφconv
      hleft_graph_eq

/--
Continuous Magnus injectivity together with the bifiltered finite-quotient calculations gives
exactness at the separated middle term for a finite-rank free pro-\(C\) presentation.
-/
theorem freeProC_exactAtSepA_of_continuousMagnus_zcBifilteredAllFiniteQuotientStages
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    [T1Space
      (ZCFreeFoxCoordinates C
        (X := ULift.{u} (Fin r)) (H := H))] :
    Function.Exact
      (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
        (G := sourceData.carrier) (H := H) C psi)
      (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := sourceData.carrier) (H := H) C
        hC.hereditary psi) := by
  let family : ULift.{u} (Fin r) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis
  let hfree :=
    freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis
  let htarget :=
    freeProCClosedGeneratedTarget_proC_of_surjective
      (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi
  let hφconv :=
    freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
      (C := C) (fun i : ULift.{u} (Fin r) => psi (family i))
  have hH : HasOpenNormalBasisInClass C H :=
    HasOpenNormalBasisInClass.of_surjective
      hC.melnikovFormation.formation
      sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass psi hpsi
  have hφHconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G := H) (fun i : ULift.{u} (Fin r) => psi (family i)) := by
    simpa [family] using
      freeProCChosenULiftFamilyOfBasisCard_image_convergesToOneAlongOpenSubgroups
        (C := C) sourceData hbasis psi.toMonoidHom
  have hφHgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : ULift.{u} (Fin r) => psi (family i))) := by
    simpa [family] using
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (C := C) sourceData hbasis psi hpsi
  let φ : ULift.{u} (Fin r) → H := fun i => psi (family i)
  let coords :=
    freeProCChosenULift_sepCoordinateEquiv
      (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi
  let Dcoords : sourceData.carrier →
      ZCFreeFoxCoordinates C
        (X := ULift.{u} (Fin r)) (H := H) :=
    fun g =>
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree φ htarget hφconv g
  have hright_graph_eq :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (C := C) hfree φ htarget hφconv =
        psi.toMonoidHom := by
    exact
      freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
        (C := C) (ULift.{u} (Fin r)) H hfree hH φ htarget hφconv
        hφHconv hφHgen psi (by intro i; rfl)
  have hcycle_closed :
      freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
        ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (C := C) φ : Subgroup
            (ZCCompletedFoxSemidirect C
              (ULift.{u} (Fin r)) H)) : Set
            (ZCCompletedFoxSemidirect C
              (ULift.{u} (Fin r)) H)) := by
    exact
      freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_zcBiAllStages_coeffGraphRelDeriv
        (C := C) hC.melnikovFormation.formation
        (X := ULift.{u} (Fin r)) (H := H) φ hH hφHgen
  refine
    exact_boundaryAddZC_sep_of_coord_cycle_lift
      (G := sourceData.carrier) (H := H) C
      hC.hereditary psi family coords ?_ Dcoords ?_ ?_
  · rfl
  · intro n
    have hcoords :
        coords.toLinearMap =
          freeProCChosenULift_sepCoordinateMap
            (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi := by
      rfl
    calc
      Dcoords n =
          freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C) hfree φ htarget hφconv n := rfl
      _ =
          freeProCChosenULift_sepCoordinateMap
            (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi
            (zcSeparatedUniversalDifferential C psi.toMonoidHom n) := by
        simpa [family, hfree, htarget, hφconv, φ] using
          (freeProCChosenULift_sepCoordinateMap_universal
            (H := H) (C := C) hC sourceData hbasis psi hpsi n).symm
      _ = coords (zcSeparatedUniversalDifferential C psi.toMonoidHom n) := by
        exact congrArg
          (fun L : ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom →ₗ[
              ZCCompletedGroupAlgebra C H]
              ZCFreeFoxCoordinates C (X := ULift.{u} (Fin r)) (H := H) =>
            L (zcSeparatedUniversalDifferential C psi.toMonoidHom n))
          hcoords.symm
  · intro v hv
    have hboundaryMap :
        blanchfieldLyndonFiniteFamilyMap
            (R := ZCCompletedGroupAlgebra C H)
            (fun i : ULift.{u} (Fin r) =>
              presentedCompletedDifferentialBoundaryProCInteger
                (G := sourceData.carrier) (H := H) C psi (family i)) =
          zcFreeGroupFoxBoundary
            C
            (FreeGroup.lift φ) :=
      finiteBLMap_boundaryZC_eq_zcFreeGroupFoxBoundary
        (G := sourceData.carrier) (H := H) C psi family
    have hvBoundary :
        zcFreeGroupFoxBoundary C (FreeGroup.lift φ) v = 0 := by
      simpa [hboundaryMap, φ] using hv
    have hy :
        ({ left := v, right := (1 : H) } :
          ZCCompletedFoxSemidirect C
            (ULift.{u} (Fin r)) H) ∈
          freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ := by
      constructor
      · rfl
      · exact hvBoundary
    have hyTarget := hcycle_closed hy
    rcases
      freeProCZCFoxSemiLiftViaClosedGen_exists_preimage_of_mem_closedGenTarget
        (C := C) hfree φ htarget hφconv hyTarget with
      ⟨g, hg⟩
    have hleft : Dcoords g = v := by
      have h := congrArg
        (fun z : ZCCompletedFoxSemidirect C
            (ULift.{u} (Fin r)) H => z.left) hg
      change
        (freeProCZCCompletedFoxSemidirectLiftViaClosedGenerated
          (C := C) hfree φ htarget hφconv g).left = v
      exact h
    have hrightLift :
        freeProCZCCompletedFoxRightHomViaClosedGenerated
            (C := C) hfree φ htarget hφconv g = 1 := by
      have h := congrArg
        (fun z : ZCCompletedFoxSemidirect C
            (ULift.{u} (Fin r)) H => z.right) hg
      simpa [freeProCZCCompletedFoxRightHomViaClosedGenerated] using h
    have hright : psi g = 1 := by
      simpa [hright_graph_eq] using hrightLift
    exact ⟨⟨g, hright⟩, hleft⟩

/--
The all-stage continuous Magnus hypothesis and surjectivity of \(\psi\) give the separated
Crowell exact sequence over \(\mathbb{Z}_C\).
-/
theorem freeProC_presentedSepCrowellZC_of_continuousMagnus_zcBiAllStages_of_psi_surj
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    Function.Injective
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := sourceData.carrier) (H := H) C psi) ∧
      Function.Exact
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := sourceData.carrier) (H := H) C psi)
        (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := sourceData.carrier) (H := H) C
          hC.hereditary psi) ∧
        Function.Exact
          (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
            (G := sourceData.carrier) (H := H) C
            hC.hereditary psi)
          (zcCompletedGroupAlgebraAugmentation C H) ∧
          Function.Surjective
            (zcCompletedGroupAlgebraAugmentation C H) :=
by
  exact
    ⟨freeProC_profKerAbBoundaryAddZCSep_inj_of_continuousMagnus
        (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi,
      freeProC_exactAtSepA_of_continuousMagnus_zcBifilteredAllFiniteQuotientStages
        (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi,
      freeProC_presentedSeparatedCrowellGroupAlgebraExactProCInteger_of_psi_surjective
        (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi,
      zcCompletedGroupAlgebraAugmentation_surjective
        (C := C) (H := H)⟩

end

end CrowellExactSequence
