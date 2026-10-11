/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CrowellExactSequence.Profinite.BlanchfieldLyndon

/-!
# Crowell Exact Sequence / Profinite / Main Theorem

This module packages the separated completed Crowell and
Blanchfield--Lyndon sequences as `FourTermLinearSequence` values and states
their exactness theorems under the required formation hypotheses.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential
open ProCGroups.ProC

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {C : ProCGroups.FiniteGroupClass.{u}}

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]

/-- The separated completed Crowell sequence over pro-`C` integer coefficients.  The additive
head map and the completed augmentation are viewed canonically as `ℤ`-linear maps. -/
def profiniteSeparatedCrowellLinearSequence
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    FourTermLinearSequence ℤ
      (ProfiniteKernelAbelianizationAdd psi)
      (ZCSeparatedCompletedDifferentialModule
        C psi.toMonoidHom)
      (ZCCompletedGroupAlgebra C H)
      (ZCCoeff C) := by
  refine FourTermLinearSequence.ofExact
    ((profiniteKernelAbelianizationBoundaryAddProCIntegerSep
      (G := sourceData.carrier) (H := H)
      C psi).toIntLinearMap)
    ((presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
      (G := sourceData.carrier) (H := H) C
      hC.hereditary
      psi).toAddMonoidHom.toIntLinearMap)
    ((zcCompletedGroupAlgebraAugmentation
      C H).toAddMonoidHom.toIntLinearMap) ?_
  rcases
      freeProC_presentedSepCrowellZC_of_continuousMagnus_zcBiAllStages_of_psi_surj
        (H := H) (C := C) hC sourceData hbasis psi hpsi with
    ⟨hinjective, hexactHead, hexactTail, hsurjective⟩
  refine ⟨hinjective, hexactHead, ?_, ?_⟩
  · change Function.Exact
      (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
        (G := sourceData.carrier) (H := H) C hC.hereditary psi)
      (zcCompletedGroupAlgebraAugmentation C H)
    exact hexactTail
  · change Function.Surjective (zcCompletedGroupAlgebraAugmentation C H)
    exact hsurjective

/--
The separated completed Crowell exact sequence over pro-\(C\) integer coefficients, packaged as
the full four-term exact sequence \(N^{\mathrm{ab}}(C)\) \(\to\) \(A_{\psi}(C)\) \(\to\)
\(\mathbb{Z}_C\llbracket H\rrbracket\) \(\to\) \(\mathbb{Z}_C\).
-/
@[simp]
theorem profiniteSeparatedCrowellLinearSequence_isExact
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    (profiniteSeparatedCrowellLinearSequence
      (H := H) (C := C) hC sourceData hbasis psi hpsi).IsExact := by
  simp only [profiniteSeparatedCrowellLinearSequence,
    FourTermLinearSequence.ofExact_isExact]

/-- The separated Blanchfield--Lyndon head map in the universe-lifted coordinates, bundled as
an integer-linear map. -/
def profiniteSeparatedBlanchfieldLyndonBoundaryLinear
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    ProfiniteKernelAbelianizationAdd psi →ₗ[ℤ]
      ZCFreeFoxCoordinates C
        (X := ULift.{u} (Fin r)) (H := H) :=
  ((freeProCChosenULift_sepCoordinateEquiv
      (H := H) (C := C) hC sourceData hbasis psi hpsi).toLinearMap.toAddMonoidHom.comp
    (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
      (G := sourceData.carrier) (H := H)
      C psi)).toIntLinearMap

/-- The canonical separated Blanchfield--Lyndon sequence in the universe-lifted coordinate
basis. -/
def profiniteSeparatedBlanchfieldLyndonLinearSequence
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    FourTermLinearSequence ℤ
      (ProfiniteKernelAbelianizationAdd psi)
      (ZCFreeFoxCoordinates C
        (X := ULift.{u} (Fin r)) (H := H))
      (ZCCompletedGroupAlgebra C H)
      (ZCCoeff C) := by
  refine FourTermLinearSequence.ofExact
    (profiniteSeparatedBlanchfieldLyndonBoundaryLinear
      (H := H) (C := C) hC sourceData hbasis psi hpsi)
    ((blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : ULift.{u} (Fin r) =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := sourceData.carrier) (H := H) C psi
          ((freeProCChosenULiftFamilyOfBasisCard
            (C := C) sourceData hbasis) i))).toAddMonoidHom.toIntLinearMap)
    ((zcCompletedGroupAlgebraAugmentation
      C H).toAddMonoidHom.toIntLinearMap) ?_
  rcases
      freeProC_presentedSepBLZC_of_continuousMagnus_zcBiAllStages_of_psi_surj
        (H := H) (C := C) hC sourceData hbasis psi hpsi with
    ⟨hinjective, hexactHead, hexactTail, hsurjective⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Function.Injective
      (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
        (H := H) (C := C) hC sourceData hbasis psi hpsi)
    exact hinjective
  · change Function.Exact
      (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
        (H := H) (C := C) hC sourceData hbasis psi hpsi)
      (blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : ULift.{u} (Fin r) =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := sourceData.carrier) (H := H) C psi
            ((freeProCChosenULiftFamilyOfBasisCard
              (C := C) sourceData hbasis) i)))
    exact hexactHead
  · change Function.Exact
      (blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : ULift.{u} (Fin r) =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := sourceData.carrier) (H := H) C psi
            ((freeProCChosenULiftFamilyOfBasisCard
              (C := C) sourceData hbasis) i)))
      (zcCompletedGroupAlgebraAugmentation C H)
    exact hexactTail
  · change Function.Surjective (zcCompletedGroupAlgebraAugmentation C H)
    exact hsurjective

/--
The separated completed Blanchfield--Lyndon exact sequence in the universe-lifted finite
coordinate basis, packaged as the full four-term exact sequence.
-/
@[simp]
theorem profiniteSeparatedBlanchfieldLyndonLinearSequence_isExact
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    (profiniteSeparatedBlanchfieldLyndonLinearSequence
      (H := H) (C := C) hC sourceData hbasis psi hpsi).IsExact := by
  simp only [profiniteSeparatedBlanchfieldLyndonLinearSequence,
    FourTermLinearSequence.ofExact_isExact]

/-- The integer-linear coordinate equivalence from concrete `Fin r` coordinates to the
universe-lifted coordinates used by the epimorphic generated-target lifting property. -/
def finULiftCompletedGroupAlgebraCoordinateLinearEquiv (r : Nat) :
    (Fin r → ZCCompletedGroupAlgebra C H) ≃ₗ[ℤ]
      (ULift.{u} (Fin r) → ZCCompletedGroupAlgebra C H) :=
  (piReindexLinearEquiv
    (R := ZCCompletedGroupAlgebra C H)
    (finULiftEquiv r)).toAddEquiv.toIntLinearEquiv

/-- The canonical concrete-coordinate BL sequence, obtained by reindexing the bundled
universe-lifted sequence once at sequence level. -/
def profiniteSeparatedBlanchfieldLyndonFinLinearSequence
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    FourTermLinearSequence ℤ
      (ProfiniteKernelAbelianizationAdd psi)
      (Fin r → ZCCompletedGroupAlgebra C H)
      (ZCCompletedGroupAlgebra C H)
      (ZCCoeff C) :=
  (profiniteSeparatedBlanchfieldLyndonLinearSequence
    (H := H) (C := C) hC sourceData hbasis psi hpsi).reindexMiddle
      (finULiftCompletedGroupAlgebraCoordinateLinearEquiv
        (H := H) (C := C) r)

/--
The separated completed Blanchfield--Lyndon exact sequence in the concrete \(\operatorname{Fin}
r\) coordinate basis, packaged as the full four-term exact sequence.
-/
@[simp]
theorem profiniteSeparatedBlanchfieldLyndonFinLinearSequence_isExact
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    (profiniteSeparatedBlanchfieldLyndonFinLinearSequence
      (H := H) (C := C) hC sourceData hbasis psi hpsi).IsExact :=
  FourTermLinearSequence.reindexMiddle_isExact
    (profiniteSeparatedBlanchfieldLyndonLinearSequence
      (H := H) (C := C) hC sourceData hbasis psi hpsi)
    (finULiftCompletedGroupAlgebraCoordinateLinearEquiv
      (H := H) (C := C) r)
    (profiniteSeparatedBlanchfieldLyndonLinearSequence_isExact
      (H := H) (C := C) hC sourceData hbasis psi hpsi)

end

end CrowellExactSequence
