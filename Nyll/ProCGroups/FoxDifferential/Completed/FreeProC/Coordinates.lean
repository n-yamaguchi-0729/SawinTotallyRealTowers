/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.NaturalTopology
import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Magnus.KernelClosedCommutator
import Nyll.ProCGroups.FreeProC.FiniteBasis

/-!
# Fox differential: completed — free pro-\(C\) — coordinates

The principal declarations in this module are:

- `freeProCChosenULift_closedGeneratedCoordinateMap`
  The coordinate map determined by the chosen \(U\)-lifts has the specified closed generated image.
- `freeProCChosenULift_sepFamilyMap`
  The separated finite-family map sends lifted chosen-basis coordinates to the separated completed
  differential module.
- `freeProCChosenULift_sepFamilyMap_single`
  The separated family map sends the standard vector at a chosen lifted basis element to its
  separated universal differential.
- `freeProCChosenULift_sepCoordinateMap_universal`
  The separated coordinate map sends the separated universal differential to the closed-generated
  Fox derivative vector.
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
The coordinate map determined by the chosen \(U\)-lifts has the specified closed generated
image.
-/
def freeProCChosenULift_closedGeneratedCoordinateMap
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    ZCCompletedDifferentialModule C psi.toMonoidHom →ₗ[
      ZCCompletedGroupAlgebra C H]
      ZCFreeFoxCoordinates C
        (X := ULift.{u} (Fin r)) (H := H) := by
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
  have hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H) :=
    HasOpenNormalBasisInClass.of_surjective hC.melnikovFormation.formation
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
  exact
    closedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := sourceData.carrier) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen

/--
The separated finite-family map sends lifted chosen-basis coordinates to the separated
completed differential module.
-/
def freeProCChosenULift_sepFamilyMap
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H) :
    ZCFreeFoxCoordinates C
        (X := ULift.{u} (Fin r)) (H := H) →ₗ[
      ZCCompletedGroupAlgebra C H]
      ZCSeparatedCompletedDifferentialModule
        C psi.toMonoidHom :=
  presentedSeparatedDifferentialFamilyMapProCInteger
    (G := sourceData.carrier) (H := H) C psi
    (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis)

omit [C.ContainsTrivialQuotients] in
/--
The separated family map sends the standard vector at a chosen lifted basis element to its separated
universal differential.
-/
@[simp 900]
theorem freeProCChosenULift_sepFamilyMap_single
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ULift.{u} (Fin r)) :
    freeProCChosenULift_sepFamilyMap
        (H := H) (C := C) sourceData hbasis psi
        (Pi.single i (1 : ZCCompletedGroupAlgebra C H)) =
      zcSeparatedUniversalDifferential
        C psi.toMonoidHom
        (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis i) := by
  exact
    presentedSeparatedDifferentialFamilyMapProCInteger_single
      (G := sourceData.carrier) (H := H) C psi
      (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) i

/-- The separated closed-generated coordinate map for the chosen finite free pro-\(C\) basis. -/
def freeProCChosenULift_sepCoordinateMap
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    [T1Space
      (ZCFreeFoxCoordinates C
        (X := ULift.{u} (Fin r)) (H := H))] :
    ZCSeparatedCompletedDifferentialModule
        C psi.toMonoidHom →ₗ[
      ZCCompletedGroupAlgebra C H]
      ZCFreeFoxCoordinates C
        (X := ULift.{u} (Fin r)) (H := H) := by
  letI :
      Nonempty
        (ZCCompletedDifferentialModuleIndex
          C psi.toMonoidHom) :=
    ⟨zcCompletedDifferentialModuleComapIndex
      (C := C) (G := sourceData.carrier) (H := H)
      hC.hereditary psi
      ((ProCGroups.Completion.ProCIntegerIndex.terminal
          (C := C) inferInstance),
        zcCompletedGroupAlgebraTopIndex C H)⟩
  have hdir :
      Directed (· ≤ ·)
        (id :
          ZCCompletedDifferentialModuleIndex
              C psi.toMonoidHom →
            ZCCompletedDifferentialModuleIndex
              C psi.toMonoidHom) :=
    directed_zcCompletedDifferentialModuleIndex
      (C := C) (G := sourceData.carrier) (H := H)
      (hC.melnikovFormation.formation)
      hC.hereditary psi
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
  have hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H) :=
    HasOpenNormalBasisInClass.of_surjective hC.melnikovFormation.formation
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
  exact
    separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger
      (G := sourceData.carrier) (H := H) C psi family hfree htarget hφconv
      hdir sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass hH hφHconv hφHgen

/--
The separated coordinate map sends the separated universal differential to the closed-generated
Fox derivative vector.
-/
@[simp 900]
theorem freeProCChosenULift_sepCoordinateMap_universal
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    [T1Space
      (ZCFreeFoxCoordinates C
        (X := ULift.{u} (Fin r)) (H := H))]
    (g : sourceData.carrier) :
    freeProCChosenULift_sepCoordinateMap
        (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi
        (zcSeparatedUniversalDifferential
          C psi.toMonoidHom g) =
      freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C)
        (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis)
        (fun i : ULift.{u} (Fin r) =>
          psi (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis i))
        (freeProCClosedGeneratedTarget_proC_of_surjective
          (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi)
        (freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
          (C := C)
          (fun i : ULift.{u} (Fin r) =>
            psi (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis i)))
        g := by
  let :
      Nonempty
        (ZCCompletedDifferentialModuleIndex
          C psi.toMonoidHom) :=
    ⟨zcCompletedDifferentialModuleComapIndex
      (C := C) (G := sourceData.carrier) (H := H)
      hC.hereditary psi
      ((ProCGroups.Completion.ProCIntegerIndex.terminal
          (C := C) inferInstance),
        zcCompletedGroupAlgebraTopIndex C H)⟩
  have hdir :
      Directed (· ≤ ·)
        (id :
          ZCCompletedDifferentialModuleIndex
              C psi.toMonoidHom →
            ZCCompletedDifferentialModuleIndex
              C psi.toMonoidHom) :=
    directed_zcCompletedDifferentialModuleIndex
      (C := C) (G := sourceData.carrier) (H := H)
      (hC.melnikovFormation.formation)
      hC.hereditary psi
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
  have hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H) :=
    HasOpenNormalBasisInClass.of_surjective hC.melnikovFormation.formation
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
  simpa [freeProCChosenULift_sepCoordinateMap, family, hfree, htarget, hφconv] using
    separatedClosedGeneratedDerivativeCoordinatesLinearMapProCInteger_universal
      (G := sourceData.carrier) (H := H) C psi family hfree htarget hφconv
      hdir sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass hH hφHconv hφHgen g

/-- The separated coordinate equivalence for the chosen finite free pro-\(C\) basis. -/
def freeProCChosenULift_sepCoordinateEquiv
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    [T1Space
      (ZCFreeFoxCoordinates C
        (X := ULift.{u} (Fin r)) (H := H))] :
    ZCSeparatedCompletedDifferentialModule
        C psi.toMonoidHom ≃ₗ[
      ZCCompletedGroupAlgebra C H]
      ZCFreeFoxCoordinates C
        (X := ULift.{u} (Fin r)) (H := H) := by
  letI :
      Nonempty
        (ZCCompletedDifferentialModuleIndex
          C psi.toMonoidHom) :=
    ⟨zcCompletedDifferentialModuleComapIndex
      (C := C) (G := sourceData.carrier) (H := H)
      hC.hereditary psi
      ((ProCGroups.Completion.ProCIntegerIndex.terminal
          (C := C) inferInstance),
        zcCompletedGroupAlgebraTopIndex C H)⟩
  have hdir :
      Directed (· ≤ ·)
        (id :
          ZCCompletedDifferentialModuleIndex
              C psi.toMonoidHom →
            ZCCompletedDifferentialModuleIndex
              C psi.toMonoidHom) :=
    directed_zcCompletedDifferentialModuleIndex
      (C := C) (G := sourceData.carrier) (H := H)
      (hC.melnikovFormation.formation)
      hC.hereditary psi
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
  have hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H) :=
    HasOpenNormalBasisInClass.of_surjective hC.melnikovFormation.formation
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
  exact
    separatedClosedGeneratedDerivativeCoordinateLinearEquivProCInteger
      (G := sourceData.carrier) (H := H) C psi family hfree htarget hφconv
      hdir sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass hH hφHconv hφHgen

end

end CrowellExactSequence
