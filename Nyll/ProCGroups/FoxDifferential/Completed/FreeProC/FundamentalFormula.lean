/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.Coordinates
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.ClosedGeneratedCycles

/-!
# Fox differential: completed — free pro-\(C\) — fundamental formula

The principal declarations in this module are:

- `freeProCChosenULift_closedGenerated_fundamental_formula_stageProj`
  At each finite stage, the chosen \(U\)-lift closed-generation map satisfies the fundamental
  formula after projection.
- `freeProCChosenULift_closedGen_fundFormula_of_stageProjsSeparate`
  Separation by finite-stage projections implies the closed-generation fundamental formula for the
  chosen \(U\)-lifts.
- `freeProCChosenULift_closedGen_fundFormula_of_relSubmoduleClosed`
  Closedness of the completed relation submodule implies the closed-generation fundamental formula
  for the chosen \(U\)-lifts.
- `freeProC_zcDiffModuleRelSubmoduleClosed_of_closedGen_fundFormula`
  The closed-generation fundamental formula implies closedness of the completed differential-module
  relation submodule.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential
open ProCGroups.ProC

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {C : ProCGroups.FiniteGroupClass.{u}}

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]

omit [C.ContainsTrivialQuotients] in
/--
At each finite stage, the chosen \(U\)-lift closed-generation map satisfies the fundamental
formula after projection.
-/
theorem freeProCChosenULift_closedGenerated_fundamental_formula_stageProj
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (i : ZCCompletedDifferentialModuleIndex
        C psi.toMonoidHom)
    (g : sourceData.carrier) :
    zcCompletedDifferentialModuleStageProjection
        C psi.toMonoidHom i
        (presentedCompletedDifferentialFamilyMapProCInteger
          (G := sourceData.carrier) (H := H) C psi
          (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis)
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C)
            (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis)
            (fun i : ULift.{u} (Fin r) =>
              psi (freeProCChosenULiftFamilyOfBasisCard
                (C := C) sourceData hbasis i))
            (freeProCClosedGeneratedTarget_proC_of_surjective
              (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi)
            (freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
              (C := C)
              (fun i : ULift.{u} (Fin r) =>
                psi (freeProCChosenULiftFamilyOfBasisCard
                  (C := C) sourceData hbasis i)))
            g)) =
      zcCompletedDifferentialModuleStageProjection
        C psi.toMonoidHom i
        (zcUniversalDifferential C psi.toMonoidHom g) := by
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
  simpa [family, hfree, htarget, hφconv] using
    closedGenerated_fundamental_formula_stageProj
      (G := sourceData.carrier) (H := H) C psi family hfree htarget hφconv
      hH hφHconv hφHgen i g

omit [C.ContainsTrivialQuotients] in
/--
Separation by finite-stage projections implies the closed-generation fundamental formula for
the chosen \(U\)-lifts.
-/
theorem freeProCChosenULift_closedGen_fundFormula_of_stageProjsSeparate
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (hsep :
      zcCompletedDifferentialModuleStageProjectionsSeparate
        C psi.toMonoidHom) :
    ∀ g : sourceData.carrier,
      presentedCompletedDifferentialFamilyMapProCInteger
          (G := sourceData.carrier) (H := H) C psi
          (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis)
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C)
            (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis)
            (fun i : ULift.{u} (Fin r) =>
              psi (freeProCChosenULiftFamilyOfBasisCard
                (C := C) sourceData hbasis i))
            (freeProCClosedGeneratedTarget_proC_of_surjective
              (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi)
            (freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
              (C := C)
              (fun i : ULift.{u} (Fin r) =>
                psi (freeProCChosenULiftFamilyOfBasisCard
                  (C := C) sourceData hbasis i)))
            g) =
        zcUniversalDifferential C psi.toMonoidHom g := by
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
  simpa [family, hfree, htarget, hφconv] using
    closedGenerated_fundamental_formula_naturalTopology_of_separating
      (G := sourceData.carrier) (H := H) C psi family hfree htarget hφconv
      hsep hH hφHconv hφHgen

/--
Closedness of the completed relation submodule implies the closed-generation fundamental
formula for the chosen \(U\)-lifts.
-/
theorem freeProCChosenULift_closedGen_fundFormula_of_relSubmoduleClosed
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (hclosed :
      zcCompletedDifferentialModuleRelationSubmoduleClosed
        C psi.toMonoidHom) :
    ∀ g : sourceData.carrier,
      presentedCompletedDifferentialFamilyMapProCInteger
          (G := sourceData.carrier) (H := H) C psi
          (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis)
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C)
            (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis)
            (fun i : ULift.{u} (Fin r) =>
              psi (freeProCChosenULiftFamilyOfBasisCard
                (C := C) sourceData hbasis i))
            (freeProCClosedGeneratedTarget_proC_of_surjective
              (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi)
            (freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
              (C := C)
              (fun i : ULift.{u} (Fin r) =>
                psi (freeProCChosenULiftFamilyOfBasisCard
                  (C := C) sourceData hbasis i)))
            g) =
        zcUniversalDifferential C psi.toMonoidHom g := by
  exact
    freeProCChosenULift_closedGen_fundFormula_of_stageProjsSeparate
      (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi
      (freeProC_zcDiffModuleStageProjsSeparate_of_relSubmoduleClosed
        (H := H) (C := C) (hC := hC) sourceData psi hclosed)

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] in
/--
The closed-generation fundamental formula implies closedness of the completed
differential-module relation submodule.
-/
theorem freeProC_zcDiffModuleRelSubmoduleClosed_of_closedGen_fundFormula
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (hfundamental :
      let htarget :=
        freeProCClosedGeneratedTarget_proC_of_surjective
          (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi
      ∀ g : sourceData.carrier,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := sourceData.carrier) (H := H) C psi
            (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis)
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C)
              (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis)
              (fun i : ULift.{u} (Fin r) =>
                psi (freeProCChosenULiftFamilyOfBasisCard
                  (C := C) sourceData hbasis i))
              htarget
              (freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
                (C := C)
                (fun i : ULift.{u} (Fin r) =>
                  psi (freeProCChosenULiftFamilyOfBasisCard
                    (C := C) sourceData hbasis i)))
              g) =
          zcUniversalDifferential C psi.toMonoidHom g) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
      C psi.toMonoidHom := by
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
  exact
    zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_hasOpenNormalBasisInClass_of_fundFormula
      (G := sourceData.carrier) (H := H) C psi family hfree htarget hφconv
      sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass hH hφHconv hφHgen
      (by simpa [family, hfree, htarget, hφconv] using hfundamental)

-- Coordinate injectivity and the fundamental formula are independent consequences of closedness.
/-- For the chosen finite free pro-`C` basis, relation-submodule closedness is equivalent to
injectivity of the closed-generated coordinate map. -/
theorem freeProC_zcDiffModuleRelSubmoduleClosed_iff_closedGenCoord_inj
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    {sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C}
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    {psi : ContinuousMonoidHom sourceData.carrier H}
    (hpsi : Function.Surjective psi) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
        C psi.toMonoidHom ↔
      Function.Injective
        (freeProCChosenULift_closedGeneratedCoordinateMap
          (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi) := by
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
  have hiff :=
    zcDiffModuleRelSubmoduleClosed_iff_closedGenCoord_inj_of_hasOpenNormalBasisInClass
      (G := sourceData.carrier) (H := H) (C := C) (psi := psi)
      (family := family) (hfree := hfree) (htarget := htarget) (hφconv := hφconv)
      hdir sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass hH hφHconv hφHgen
  simpa [freeProCChosenULift_closedGeneratedCoordinateMap, family, hfree, htarget, hφconv,
    hH, hφHconv, hφHgen] using hiff

/--
Injectivity of the closed-generated coordinate map implies closedness of the completed
differential-module relation submodule.
-/
theorem freeProC_zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_inj
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (hcoord_inj :
      Function.Injective
        (freeProCChosenULift_closedGeneratedCoordinateMap
          (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi)) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
      C psi.toMonoidHom :=
  (freeProC_zcDiffModuleRelSubmoduleClosed_iff_closedGenCoord_inj
    (H := H) (C := C) (hC := hC) (sourceData := sourceData) hbasis
    (psi := psi) hpsi).2 hcoord_inj

/--
Injectivity of the closed-generated coordinate map implies the closed-generated fundamental
formula for the chosen \(U\)-lifts.
-/
theorem freeProCChosenULift_closedGen_fundFormula_of_closedGenCoord_inj
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (hcoord_inj :
      Function.Injective
        (freeProCChosenULift_closedGeneratedCoordinateMap
          (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi)) :
    let htarget :=
      freeProCClosedGeneratedTarget_proC_of_surjective
        (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi
    ∀ g : sourceData.carrier,
      presentedCompletedDifferentialFamilyMapProCInteger
          (G := sourceData.carrier) (H := H) C psi
          (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis)
          (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
            (C := C)
            (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis)
            (fun i : ULift.{u} (Fin r) =>
              psi (freeProCChosenULiftFamilyOfBasisCard
                (C := C) sourceData hbasis i))
            htarget
            (freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
              (C := C)
              (fun i : ULift.{u} (Fin r) =>
                psi (freeProCChosenULiftFamilyOfBasisCard
                  (C := C) sourceData hbasis i)))
            g) =
        zcUniversalDifferential C psi.toMonoidHom g := by
  exact
    freeProCChosenULift_closedGen_fundFormula_of_relSubmoduleClosed
      (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi
      (freeProC_zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_inj
        (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi hcoord_inj)

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] in
/--
The closed-generation fundamental formula supplies the required chosen-\(U\)-lift basis data
for \(A\).
-/
theorem chosenULift_hbasis_A_of_closedGen_fundFormula
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
    (hfundamental :
      ∀ g : sourceData.carrier,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := sourceData.carrier) (H := H) C psi
            (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis)
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C)
              (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis)
              (fun i : ULift.{u} (Fin r) =>
                psi (freeProCChosenULiftFamilyOfBasisCard
                  (C := C) sourceData hbasis i))
              htarget
              (freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
                (C := C)
                (fun i : ULift.{u} (Fin r) =>
                  psi (freeProCChosenULiftFamilyOfBasisCard
                    (C := C) sourceData hbasis i)))
              g) =
          zcUniversalDifferential C psi.toMonoidHom g) :
    IsPresentedCompletedDifferentialFamilyBasisProCInteger
      (G := sourceData.carrier) (H := H) C psi
      (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) := by
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
  exact
    isPresentedCompletedDifferentialFamilyBasisZC_of_closedGen_fundFormula
      (G := sourceData.carrier) (H := H) C psi family hfree
      (by simpa [family] using htarget) hφconv hH hφHconv hφHgen
      (by simpa [family, hfree, hφconv] using hfundamental)

omit [C.ContainsTrivialQuotients] in
/--
Continuity of the closed-generated and universal differential formulas promotes the chosen lifted
finite family to a basis of the presented completed differential module.
-/
theorem chosenULift_hbasis_A_of_closedGen_fundFormula_continuous
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    [TopologicalSpace (ZCCompletedDifferentialModule
      C psi.toMonoidHom)]
    [T2Space (ZCCompletedDifferentialModule
      C psi.toMonoidHom)]
    (htarget :
      HasOpenNormalBasisInClass C
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (C := C)
          (fun i : ULift.{u} (Fin r) =>
            psi (freeProCChosenULiftFamilyOfBasisCard
              (C := C) sourceData hbasis i)) : Subgroup
            (ZCCompletedFoxSemidirect
              C (ULift.{u} (Fin r)) H)))
    (hmodule_continuous :
      Continuous
        (fun g : sourceData.carrier =>
          presentedCompletedDifferentialFamilyMapProCInteger
              (G := sourceData.carrier) (H := H) C psi
              (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis)
              (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
                (C := C)
                (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree
                  (C := C) sourceData hbasis)
                (fun i : ULift.{u} (Fin r) =>
                  psi (freeProCChosenULiftFamilyOfBasisCard
                    (C := C) sourceData hbasis i))
                htarget
                (freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
                  (C := C)
                  (fun i : ULift.{u} (Fin r) =>
                    psi (freeProCChosenULiftFamilyOfBasisCard
                      (C := C) sourceData hbasis i)))
                g)))
    (huniv_continuous :
      Continuous
        (fun g : sourceData.carrier =>
          zcUniversalDifferential C psi.toMonoidHom g)) :
    IsPresentedCompletedDifferentialFamilyBasisProCInteger
      (G := sourceData.carrier) (H := H) C psi
      (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) := by
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
  have hfundamental :
      ∀ g : sourceData.carrier,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := sourceData.carrier) (H := H) C psi family
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C) hfree (fun i : ULift.{u} (Fin r) => psi (family i))
              (by simpa [family] using htarget) hφconv g) =
          zcUniversalDifferential C psi.toMonoidHom g :=
    closedGenerated_fundamental_formula_of_continuous
      (G := sourceData.carrier) (H := H) C psi family hfree
      (by simpa [family] using htarget) hφconv hH hφHconv hφHgen
      (by simpa [family, hfree, hφconv] using hmodule_continuous)
      (by simpa using huniv_continuous)
  exact
    chosenULift_hbasis_A_of_closedGen_fundFormula
      (H := H) (C := C) hForm sourceData hbasis psi hpsi htarget
      (by simpa [family, hfree, hφconv] using hfundamental)

/--
Closedness of the completed relation submodule gives the required basis-indexed
chosen-\(U\)-lift family in the Crowell module \(A\).
-/
theorem freeProCChosenULiftFamilyOfBasisCard_hbasis_A_of_relationSubmoduleClosed
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (hclosed :
      zcCompletedDifferentialModuleRelationSubmoduleClosed
        C psi.toMonoidHom) :
    IsPresentedCompletedDifferentialFamilyBasisProCInteger
      (G := sourceData.carrier) (H := H) C psi
      (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) := by
  let htarget :=
    freeProCClosedGeneratedTarget_proC_of_surjective
      (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi
  have hfundamental :
      ∀ g : sourceData.carrier,
        presentedCompletedDifferentialFamilyMapProCInteger
            (G := sourceData.carrier) (H := H) C psi
            (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis)
            (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
              (C := C)
              (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis)
              (fun i : ULift.{u} (Fin r) =>
                psi (freeProCChosenULiftFamilyOfBasisCard
                  (C := C) sourceData hbasis i))
              htarget
              (freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
                (C := C)
                (fun i : ULift.{u} (Fin r) =>
                  psi (freeProCChosenULiftFamilyOfBasisCard
                    (C := C) sourceData hbasis i)))
              g) =
          zcUniversalDifferential C psi.toMonoidHom g := by
    simpa [htarget] using
      freeProCChosenULift_closedGen_fundFormula_of_relSubmoduleClosed
        (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi hclosed
  exact
    chosenULift_hbasis_A_of_closedGen_fundFormula
      (H := H) (C := C) hC.melnikovFormation.formation
      sourceData hbasis psi hpsi htarget hfundamental

/--
Injectivity of the closed-generated coordinate map gives the finite \(A_{\psi}(C)\)-basis
theorem for the chosen lifted basis family.
-/
theorem freeProCChosenULiftFamilyOfBasisCard_hbasis_A_of_closedGenCoord_inj
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (hcoord_inj :
      Function.Injective
        (freeProCChosenULift_closedGeneratedCoordinateMap
          (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi)) :
    IsPresentedCompletedDifferentialFamilyBasisProCInteger
      (G := sourceData.carrier) (H := H) C psi
      (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) :=
  freeProCChosenULiftFamilyOfBasisCard_hbasis_A_of_relationSubmoduleClosed
    (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi
    (freeProC_zcDiffModuleRelSubmoduleClosed_of_closedGenCoord_inj
      (H := H) (C := C) (hC := hC) sourceData hbasis psi hpsi hcoord_inj)

end

end CrowellExactSequence
