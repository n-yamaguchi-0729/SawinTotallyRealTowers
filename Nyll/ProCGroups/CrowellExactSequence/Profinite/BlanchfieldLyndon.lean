/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CrowellExactSequence.Profinite.FreeExactness
import Nyll.ProCGroups.FreeProC.FiniteBasis

/-!
# Crowell Exact Sequence / Profinite / Blanchfield Lyndon

This module gives the completed Blanchfield--Lyndon boundary maps and exact
sequences in canonical lifted coordinates.  Concrete `Fin n` formulations are
obtained by reindexing only at their public presentation boundary.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential
open ProCGroups.ProC

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {C : ProCGroups.FiniteGroupClass.{u}}

/--
The first pro-\(C\) Blanchfield--Lyndon boundary map reads the kernel-abelianization boundary
in the chosen \(A_{\psi}(C)\) coordinates.
-/
def freeProCBlanchfieldLyndonBoundaryProCInteger
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := sourceData.carrier) (H := H) C psi
        (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis))
    (hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger
        (G := sourceData.carrier) (H := H) C psi) :
    ProfiniteKernelAbelianizationAdd psi →
      ULift.{u} (Fin r) → ZCCompletedGroupAlgebra C H :=
  fun x =>
    presentedCompletedDifferentialFamilyCoordinatesProCInteger
      (G := sourceData.carrier) (H := H) C psi
      (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) hbasis_A
      (profiniteKernelAbelianizationBoundaryAddProCInteger
        (G := sourceData.carrier) (H := H) C psi hwell_dN x)

/--
Exactness at the \(A\)-term is equivalent to the coordinatewise Blanchfield--Lyndon exactness
condition.
-/
theorem freeProC_exactAtA_iff_blanchfieldLyndonExactAtCoordinatesProCInteger
    {sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C}
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    {psi : ContinuousMonoidHom sourceData.carrier H}
    (hbasis_A :
      IsPresentedCompletedDifferentialFamilyBasisProCInteger
        (G := sourceData.carrier) (H := H) C psi
        (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis))
    {hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger
        (G := sourceData.carrier) (H := H) C psi} :
    Function.Exact
        (profiniteKernelAbelianizationBoundaryAddProCInteger
          (G := sourceData.carrier) (H := H) C psi hwell_dN)
        (presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
          (G := sourceData.carrier) (H := H) C psi) ↔
      Function.Exact
        (freeProCBlanchfieldLyndonBoundaryProCInteger
          (H := H) (C := C) sourceData hbasis psi hbasis_A hwell_dN)
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra C H)
          (fun i : ULift.{u} (Fin r) =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := sourceData.carrier) (H := H) C psi
              ((freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) i))) := by
  let family : ULift.{u} (Fin r) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis
  let dN :=
    profiniteKernelAbelianizationBoundaryAddProCInteger
      (G := sourceData.carrier) (H := H) C psi hwell_dN
  let coords :=
    presentedCompletedDifferentialFamilyCoordinatesProCInteger
      (G := sourceData.carrier) (H := H) C psi family hbasis_A
  let delta :=
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger
      (G := sourceData.carrier) (H := H) C psi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : ULift.{u} (Fin r) =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := sourceData.carrier) (H := H) C psi (family i))
  have hblDelta_comp : delta.comp coords.symm.toLinearMap = blDelta := by
    rw [presentedCompletedDifferentialFamilyCoordinatesProCInteger_symm_toLinearMap]
    exact
      presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
        (G := sourceData.carrier) (H := H) C psi family
  have hblDelta_apply (y) : blDelta y = delta (coords.symm y) := by
    have h := congrArg (fun f => f y) hblDelta_comp
    change delta (coords.symm y) = blDelta y at h
    exact h.symm
  change
    Function.Exact dN delta ↔
      Function.Exact (fun x => coords (dN x)) blDelta
  constructor
  · intro hexact_A y
    constructor
    · intro hy
      have hy_delta : delta (coords.symm y) = 0 := by
        simpa [hblDelta_apply y] using hy
      rcases (hexact_A (coords.symm y)).1 hy_delta with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      calc
        coords (dN x) = coords (coords.symm y) := congrArg coords hx
        _ = y := coords.apply_symm_apply y
    · rintro ⟨x, rfl⟩
      have hker : delta (dN x) = 0 :=
        (hexact_A (dN x)).2 ⟨x, rfl⟩
      calc
        blDelta (coords (dN x)) = delta (coords.symm (coords (dN x))) :=
          hblDelta_apply (coords (dN x))
        _ = delta (dN x) := by rw [coords.symm_apply_apply]
        _ = 0 := hker
  · intro hexact_BL y
    constructor
    · intro hy
      have hy_bl : blDelta (coords y) = 0 := by
        calc
          blDelta (coords y) = delta (coords.symm (coords y)) :=
            hblDelta_apply (coords y)
          _ = delta y := by rw [coords.symm_apply_apply]
          _ = 0 := hy
      rcases (hexact_BL (coords y)).1 hy_bl with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply coords.injective
      simpa using hx
    · rintro ⟨x, rfl⟩
      have hbl : blDelta (coords (dN x)) = 0 :=
        (hexact_BL (coords (dN x))).2 ⟨x, rfl⟩
      calc
        delta (dN x) = delta (coords.symm (coords (dN x))) := by
          rw [coords.symm_apply_apply]
        _ = blDelta (coords (dN x)) := by
          rw [hblDelta_apply]
        _ = 0 := hbl

/--
The separated pro-\(C\) Blanchfield--Lyndon boundary map reads the separated
kernel-abelianization boundary in the chosen coordinates.
-/
def freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    ProfiniteKernelAbelianizationAdd psi →
      ZCFreeFoxCoordinates C
        (X := ULift.{u} (Fin r)) (H := H) :=
  fun x =>
    freeProCChosenULift_sepCoordinateEquiv
      (H := H) (C := C) hC sourceData hbasis psi hpsi
      (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
        (G := sourceData.carrier) (H := H) C psi x)

/--
Exactness at the separated Crowell module is equivalent to Blanchfield--Lyndon exactness in
pro-\(C\)-integer coordinates.
-/
theorem freeProC_exactAtSepA_iff_blanchfieldLyndonExactAtCoordinatesProCInteger
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    {sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C}
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    {psi : ContinuousMonoidHom sourceData.carrier H}
    (hpsi : Function.Surjective psi) :
    Function.Exact
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := sourceData.carrier) (H := H) C psi)
        (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := sourceData.carrier) (H := H) C
          hC.hereditary psi) ↔
      Function.Exact
        (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
          (H := H) (C := C) hC sourceData hbasis psi hpsi)
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra C H)
          (fun i : ULift.{u} (Fin r) =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := sourceData.carrier) (H := H) C psi
              ((freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) i))) := by
  let family : ULift.{u} (Fin r) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis
  let dN :=
    profiniteKernelAbelianizationBoundaryAddProCIntegerSep
      (G := sourceData.carrier) (H := H) C psi
  let coords :=
    freeProCChosenULift_sepCoordinateEquiv
      (H := H) (C := C) hC sourceData hbasis psi hpsi
  let delta :=
    presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
      (G := sourceData.carrier) (H := H) C
      hC.hereditary psi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : ULift.{u} (Fin r) =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := sourceData.carrier) (H := H) C psi (family i))
  have hcoords_symm :
      coords.symm.toLinearMap =
        freeProCChosenULift_sepFamilyMap
          (H := H) (C := C) sourceData hbasis psi := by
    rfl
  have hblDelta_comp : delta.comp coords.symm.toLinearMap = blDelta := by
    rw [hcoords_symm]
    exact
      presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger_comp_familyMap
        (G := sourceData.carrier) (H := H) C
        hC.hereditary psi family
  have hblDelta_apply (y) : blDelta y = delta (coords.symm y) := by
    have h := congrArg (fun f => f y) hblDelta_comp
    change delta (coords.symm y) = blDelta y at h
    exact h.symm
  change
    Function.Exact dN delta ↔
      Function.Exact (fun x => coords (dN x)) blDelta
  constructor
  · intro hexact_A y
    constructor
    · intro hy
      have hy_delta : delta (coords.symm y) = 0 := by
        simpa [hblDelta_apply y] using hy
      rcases (hexact_A (coords.symm y)).1 hy_delta with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      calc
        coords (dN x) = coords (coords.symm y) := congrArg coords hx
        _ = y := coords.apply_symm_apply y
    · rintro ⟨x, rfl⟩
      have hker : delta (dN x) = 0 :=
        (hexact_A (dN x)).2 ⟨x, rfl⟩
      calc
        blDelta (coords (dN x)) = delta (coords.symm (coords (dN x))) :=
          hblDelta_apply (coords (dN x))
        _ = delta (dN x) := by rw [coords.symm_apply_apply]
        _ = 0 := hker
  · intro hexact_BL y
    constructor
    · intro hy
      have hy_bl : blDelta (coords y) = 0 := by
        calc
          blDelta (coords y) = delta (coords.symm (coords y)) :=
            hblDelta_apply (coords y)
          _ = delta y := by rw [coords.symm_apply_apply]
          _ = 0 := hy
      rcases (hexact_BL (coords y)).1 hy_bl with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply coords.injective
      simpa using hx
    · rintro ⟨x, rfl⟩
      have hbl : blDelta (coords (dN x)) = 0 :=
        (hexact_BL (coords (dN x))).2 ⟨x, rfl⟩
      calc
        delta (dN x) = delta (coords.symm (coords (dN x))) := by
          rw [coords.symm_apply_apply]
        _ = blDelta (coords (dN x)) := (hblDelta_apply (coords (dN x))).symm
        _ = 0 := hbl

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]

/--
For a surjective \(\psi\), the presented Blanchfield--Lyndon group-algebra sequence over
\(\mathbb{Z}_C\) is exact.
-/
theorem freeProC_presentedBlanchfieldLyndonGAExactZC_of_psi_surj
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    Function.Exact
      (blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : Fin r =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := sourceData.carrier) (H := H) C psi
            (freeProCChosenULiftFamilyOfBasisCard
              (C := C) sourceData hbasis (ULift.up i))))
      (zcCompletedGroupAlgebraAugmentation C H) := by
  let family : Fin r → sourceData.carrier :=
    fun i =>
      freeProCChosenULiftFamilyOfBasisCard
        (C := C) sourceData hbasis (ULift.up i)
  have htargetGen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : Fin r => psi (family i))) := by
    have hgen :=
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (C := C) sourceData hbasis psi hpsi
    have hrange :
        Set.range (fun i : Fin r => psi (family i)) =
          Set.range (fun i : ULift.{u} (Fin r) =>
            psi (freeProCChosenULiftFamilyOfBasisCard
              (C := C) sourceData hbasis i)) := by
      ext h
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨ULift.up i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.down, by cases i; rfl⟩
    rw [hrange]
    exact hgen
  simpa [family] using
    exact_blanchfieldLyndonFiniteFamilyMap_boundary_family_of_topologicallyGenerates
      (G := sourceData.carrier) (H := H) C
      hForm psi family htargetGen

/--
For a surjective \(\psi\), the separated presented Blanchfield--Lyndon group-algebra sequence
over \(\mathbb{Z}_C\) is exact.
-/
theorem freeProC_presentedSepBlanchfieldLyndonGAExactZC_of_psi_surj
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    Function.Exact
      (blanchfieldLyndonFiniteFamilyMap
        (R := ZCCompletedGroupAlgebra C H)
        (fun i : ULift.{u} (Fin r) =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := sourceData.carrier) (H := H) C psi
            ((freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) i)))
      (zcCompletedGroupAlgebraAugmentation C H) := by
  let family : ULift.{u} (Fin r) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis
  have htargetGen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : ULift.{u} (Fin r) => psi (family i))) := by
    simpa [family] using
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (C := C) sourceData hbasis psi hpsi
  simpa [family] using
    exact_blanchfieldLyndonFiniteFamilyMap_boundary_family_of_topologicallyGenerates
      (G := sourceData.carrier) (H := H) C
      hForm psi family htargetGen

/--
The all-stage continuous Magnus hypothesis and surjectivity of \(\psi\) give the separated
Blanchfield--Lyndon exact sequence over \(\mathbb{Z}_C\).
-/
theorem freeProC_presentedSepBLZC_of_continuousMagnus_zcBiAllStages_of_psi_surj
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    Function.Injective
        (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
          (H := H) (C := C) hC sourceData hbasis psi hpsi) ∧
      Function.Exact
          (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
            (H := H) (C := C) hC sourceData hbasis psi hpsi)
          (blanchfieldLyndonFiniteFamilyMap
            (R := ZCCompletedGroupAlgebra C H)
            (fun i : ULift.{u} (Fin r) =>
              presentedCompletedDifferentialBoundaryProCInteger
                (G := sourceData.carrier) (H := H) C psi
                ((freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) i))) ∧
      Function.Exact
          (blanchfieldLyndonFiniteFamilyMap
            (R := ZCCompletedGroupAlgebra C H)
            (fun i : ULift.{u} (Fin r) =>
              presentedCompletedDifferentialBoundaryProCInteger
                (G := sourceData.carrier) (H := H) C psi
                ((freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) i)))
          (zcCompletedGroupAlgebraAugmentation C H) ∧
      Function.Surjective
        (zcCompletedGroupAlgebraAugmentation C H) :=
by
  let dN :=
    profiniteKernelAbelianizationBoundaryAddProCIntegerSep
      (G := sourceData.carrier) (H := H) C psi
  let coords :=
    freeProCChosenULift_sepCoordinateEquiv
      (H := H) (C := C) hC sourceData hbasis psi hpsi
  let blDelta :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : ULift.{u} (Fin r) =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := sourceData.carrier) (H := H) C psi
          ((freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) i))
  have hinj_dN :
      Function.Injective dN :=
    freeProC_profKerAbBoundaryAddZCSep_inj_of_continuousMagnus
      (H := H) (C := C) hC sourceData hbasis psi hpsi
  have hexact_A :
      Function.Exact dN
        (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := sourceData.carrier) (H := H) C
          hC.hereditary psi) :=
    freeProC_exactAtSepA_of_continuousMagnus_zcBifilteredAllFiniteQuotientStages
      (H := H) (C := C) hC sourceData hbasis psi hpsi
  have hexact_BL_A :
      Function.Exact
          (fun x : ProfiniteKernelAbelianizationAdd psi => coords (dN x))
          blDelta :=
    (freeProC_exactAtSepA_iff_blanchfieldLyndonExactAtCoordinatesProCInteger
      (H := H) (C := C) hC (sourceData := sourceData) hbasis
      (psi := psi) hpsi).1 hexact_A
  change
    Function.Injective
        (fun x : ProfiniteKernelAbelianizationAdd psi => coords (dN x)) ∧
      Function.Exact
          (fun x : ProfiniteKernelAbelianizationAdd psi => coords (dN x)) blDelta ∧
      Function.Exact blDelta
          (zcCompletedGroupAlgebraAugmentation C H) ∧
      Function.Surjective
        (zcCompletedGroupAlgebraAugmentation C H)
  refine ⟨?_, hexact_BL_A, ?_, ?_⟩
  · intro x y hxy
    exact hinj_dN (coords.injective hxy)
  · exact
      freeProC_presentedSepBlanchfieldLyndonGAExactZC_of_psi_surj
        (H := H) (C := C) hC.melnikovFormation.formation
        sourceData hbasis psi hpsi
  · exact
      zcCompletedGroupAlgebraAugmentation_surjective
        (C := C) (H := H)

/--
The finite-index display reindexes the separated Blanchfield--Lyndon boundary map from
\(\mathrm{ULift}(\mathrm{Fin}\, r)\) to \(\mathrm{Fin}\, r\).
-/
def freeProCSeparatedBlanchfieldLyndonBoundaryFinProCInteger
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    ProfiniteKernelAbelianizationAdd psi →
      Fin r → ZCCompletedGroupAlgebra C H :=
  let e : Fin r ≃ ULift.{u} (Fin r) := finULiftEquiv r
  fun x =>
    (piReindexLinearEquiv
      (R := ZCCompletedGroupAlgebra C H) e).symm
      (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
        (H := H) (C := C) hC sourceData hbasis psi hpsi x)

/--
Exactness at the separated Crowell module is equivalent to finite-coordinate
Blanchfield--Lyndon exactness over the pro-\(C\) integers.
-/
theorem freeProC_exactAtSepA_iff_blanchfieldLyndonExactAtFinCoordinatesProCInteger
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    {sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C}
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    {psi : ContinuousMonoidHom sourceData.carrier H}
    (hpsi : Function.Surjective psi) :
    Function.Exact
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := sourceData.carrier) (H := H) C psi)
        (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := sourceData.carrier) (H := H) C
          hC.hereditary psi) ↔
      Function.Exact
        (freeProCSeparatedBlanchfieldLyndonBoundaryFinProCInteger
          (H := H) (C := C) hC sourceData hbasis psi hpsi)
        (blanchfieldLyndonFiniteFamilyMap
          (R := ZCCompletedGroupAlgebra C H)
          (fun i : Fin r =>
            presentedCompletedDifferentialBoundaryProCInteger
              (G := sourceData.carrier) (H := H) C psi
              (freeProCChosenULiftFamilyOfBasisCard
                (C := C) sourceData hbasis (ULift.up i)))) := by
  let e : Fin r ≃ ULift.{u} (Fin r) := finULiftEquiv r
  let L :
      (Fin r → ZCCompletedGroupAlgebra C H) ≃ₗ[
        ZCCompletedGroupAlgebra C H]
        (ULift.{u} (Fin r) →
          ZCCompletedGroupAlgebra C H) :=
    piReindexLinearEquiv
      (R := ZCCompletedGroupAlgebra C H) e
  let blULift :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : ULift.{u} (Fin r) =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := sourceData.carrier) (H := H) C psi
          ((freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) i))
  let blFin :=
    blanchfieldLyndonFiniteFamilyMap
      (R := ZCCompletedGroupAlgebra C H)
      (fun i : Fin r =>
        presentedCompletedDifferentialBoundaryProCInteger
          (G := sourceData.carrier) (H := H) C psi
          (freeProCChosenULiftFamilyOfBasisCard
            (C := C) sourceData hbasis (ULift.up i)))
  have hblFin :
      blFin = blULift.comp L.toLinearMap := by
    simpa [blFin, blULift, L, e, finULiftEquiv, freeProCChosenULiftFamilyOfBasisCard] using
      (finiteFamilyLinearMap_reindex
        (R := ZCCompletedGroupAlgebra C H)
        e
        (fun i : ULift.{u} (Fin r) =>
          presentedCompletedDifferentialBoundaryProCInteger
            (G := sourceData.carrier) (H := H) C psi
            ((freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) i)))
  have hULiftIff :=
    freeProC_exactAtSepA_iff_blanchfieldLyndonExactAtCoordinatesProCInteger
      (H := H) (C := C) hC (sourceData := sourceData) hbasis
      (psi := psi) hpsi
  have htransport :
      Function.Exact
          (fun x : ProfiniteKernelAbelianizationAdd psi =>
            L.symm
              (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
                (H := H) (C := C) hC sourceData hbasis psi hpsi x))
          (fun y : Fin r → ZCCompletedGroupAlgebra C H =>
            blULift (L y)) ↔
        Function.Exact
          (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
            (H := H) (C := C) hC sourceData hbasis psi hpsi)
          blULift :=
    Function.Exact.linearEquiv_symm_comp_comp_iff
      (R := ZCCompletedGroupAlgebra C H) L
  change
    Function.Exact
        (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := sourceData.carrier) (H := H) C psi)
        (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := sourceData.carrier) (H := H) C
          hC.hereditary psi) ↔
      Function.Exact
        (fun x : ProfiniteKernelAbelianizationAdd psi =>
          L.symm
            (freeProCSeparatedBlanchfieldLyndonBoundaryProCInteger
              (H := H) (C := C) hC sourceData hbasis psi hpsi x))
        blFin
  rw [hblFin]
  exact hULiftIff.trans htransport.symm

/--
The all-stage continuous Magnus hypothesis and surjectivity of \(\psi\) give the
finite-coordinate separated Blanchfield--Lyndon exact sequence over \(\mathbb{Z}_C\).
-/
theorem freeProC_presentedSepBLFinZC_of_continuousMagnus_zcBiAllStages_of_psi_surj
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    Function.Injective
        (freeProCSeparatedBlanchfieldLyndonBoundaryFinProCInteger
          (H := H) (C := C) hC sourceData hbasis psi hpsi) ∧
      Function.Exact
          (freeProCSeparatedBlanchfieldLyndonBoundaryFinProCInteger
            (H := H) (C := C) hC sourceData hbasis psi hpsi)
          (blanchfieldLyndonFiniteFamilyMap
            (R := ZCCompletedGroupAlgebra C H)
            (fun i : Fin r =>
              presentedCompletedDifferentialBoundaryProCInteger
                (G := sourceData.carrier) (H := H) C psi
                (freeProCChosenULiftFamilyOfBasisCard
                  (C := C) sourceData hbasis (ULift.up i)))) ∧
      Function.Exact
          (blanchfieldLyndonFiniteFamilyMap
            (R := ZCCompletedGroupAlgebra C H)
            (fun i : Fin r =>
              presentedCompletedDifferentialBoundaryProCInteger
                (G := sourceData.carrier) (H := H) C psi
                (freeProCChosenULiftFamilyOfBasisCard
                  (C := C) sourceData hbasis (ULift.up i))))
          (zcCompletedGroupAlgebraAugmentation C H) ∧
      Function.Surjective
        (zcCompletedGroupAlgebraAugmentation C H) :=
by
  let e : Fin r ≃ ULift.{u} (Fin r) := finULiftEquiv r
  let L :
      (Fin r → ZCCompletedGroupAlgebra C H) ≃ₗ[
        ZCCompletedGroupAlgebra C H]
        (ULift.{u} (Fin r) →
          ZCCompletedGroupAlgebra C H) :=
    piReindexLinearEquiv
      (R := ZCCompletedGroupAlgebra C H) e
  let dN :=
    profiniteKernelAbelianizationBoundaryAddProCIntegerSep
      (G := sourceData.carrier) (H := H) C psi
  let coords :=
    freeProCChosenULift_sepCoordinateEquiv
      (H := H) (C := C) hC sourceData hbasis psi hpsi
  have hinj_dN :
      Function.Injective dN :=
    freeProC_profKerAbBoundaryAddZCSep_inj_of_continuousMagnus
      (H := H) (C := C) hC sourceData hbasis psi hpsi
  have hexact_A :
      Function.Exact dN
        (presentedSeparatedDifferentialToCompletedGroupAlgebraProCInteger
          (G := sourceData.carrier) (H := H) C
          hC.hereditary psi) :=
    freeProC_exactAtSepA_of_continuousMagnus_zcBifilteredAllFiniteQuotientStages
      (H := H) (C := C) hC sourceData hbasis psi hpsi
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    change L.symm (coords (dN x)) = L.symm (coords (dN y)) at hxy
    exact hinj_dN (coords.injective (L.symm.injective hxy))
  · exact
      (freeProC_exactAtSepA_iff_blanchfieldLyndonExactAtFinCoordinatesProCInteger
        (H := H) (C := C) hC (sourceData := sourceData) hbasis
        (psi := psi) hpsi).1 hexact_A
  · exact
      freeProC_presentedBlanchfieldLyndonGAExactZC_of_psi_surj
        (H := H) (C := C) hC.melnikovFormation.formation
        sourceData hbasis psi hpsi
  · exact
      zcCompletedGroupAlgebraAugmentation_surjective
        (C := C) (H := H)

end

end CrowellExactSequence
