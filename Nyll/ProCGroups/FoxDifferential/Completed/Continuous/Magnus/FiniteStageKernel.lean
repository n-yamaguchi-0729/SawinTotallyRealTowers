/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Magnus.ClosedGeneratedVector
import Nyll.ProCGroups.FoxDifferential.Completed.Comparison.FiniteStage
import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Naturality
import Nyll.ProCGroups.FreeProC.FiniteBasis

/-!
# Fox Differential / Completed / Continuous Magnus / Finite Stage Kernel

This module compares the completed Magnus map with its finite quotient stages
and characterizes the kernel through the corresponding discrete Fox
calculation.
-/

namespace CrowellExactSequence

noncomputable section

open ProCGroups.ProC
open ProCGroups.ProC.HasOpenNormalBasisInClass
open FoxDifferential

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {C : ProCGroups.FiniteGroupClass.{u}}

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]

section ProfiniteTarget

variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] in
/--
Free-group comparison for the concrete closed-generated continuous Fox vector, with the right
component already identified with the presentation map.
-/
theorem freeFoxDerivVec_eq_freeProCClosedGenFoxVectorZC_comp_lift_mapTarget
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H) (hpsi : Function.Surjective psi)
    (htarget :
      ProCGroups.ProC.HasOpenNormalBasisInClass C
        (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (C := C)
          (fun i : ULift.{u} (Fin r) =>
            psi (freeProCChosenULiftFamilyOfBasisCard
              (C := C) sourceData hbasis i)) : Subgroup
            (FoxDifferential.ZCCompletedFoxSemidirect
              C (ULift.{u} (Fin r)) H)))
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (η : H →ₜ* K) (w : FreeGroup (ULift.{u} (Fin r))) :
    FoxDifferential.zcFreeGroupFoxDerivativeVector C
        (η.toMonoidHom.comp
          (psi.toMonoidHom.comp
            (FreeGroup.lift
              (freeProCChosenULiftFamilyOfBasisCard
                (C := C) sourceData hbasis)))) w =
      FoxDifferential.zcFreeFoxCoordinatesMap
        (X := ULift.{u} (Fin r)) C hC η
        (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
          (H := H) (C := C) sourceData hbasis psi htarget
          ((FreeGroup.lift
            (freeProCChosenULiftFamilyOfBasisCard
              (C := C) sourceData hbasis)) w)) := by
  let X : Type u := ULift.{u} (Fin r)
  let ι : X → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis
  let hfree := freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis
  let φ : X → H := fun i => psi (ι i)
  let hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (C := C) φ : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect C X H)))
        (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
          (C := C) φ) :=
    FoxDifferential.freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
      (C := C) φ
  have hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H) :=
    HasOpenNormalBasisInClass.of_surjective hForm
      sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass psi hpsi
  have hφHconv : ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups (G := H) φ := by
    simpa [φ, ι] using
      freeProCChosenULiftFamilyOfBasisCard_image_convergesToOneAlongOpenSubgroups
        (C := C) sourceData hbasis psi.toMonoidHom
  have hφHgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ) := by
    simpa [φ, ι] using
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (C := C) sourceData hbasis psi hpsi
  have hright :
      FoxDifferential.freeProCZCCompletedFoxRightHomViaClosedGenerated
          (C := C) hfree φ htarget hφconv =
        psi.toMonoidHom := by
    have hright_lift :=
      FoxDifferential.freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_lift
        (C := C) X H hfree hH φ htarget hφconv hφHconv hφHgen
    have hlift :
        hfree.lift hH φ hφHconv hφHgen = psi.toMonoidHom := by
      exact
        (hfree.lift_unique hH φ hφHconv hφHgen psi.continuous_toFun (by
          intro i
          rfl)).symm
    exact hright_lift.trans hlift
  have hcomp :=
    FoxDifferential.zcFreeFoxDerivVec_eq_freeProCDerivVecViaClosedGen_comp_lift_mapTarget
      (C := C) hfree φ htarget hφconv hC η w
  have hcoeff :
      η.toMonoidHom.comp
          ((FoxDifferential.freeProCZCCompletedFoxRightHomViaClosedGenerated
            (C := C) hfree φ htarget hφconv).comp (FreeGroup.lift ι)) =
        η.toMonoidHom.comp (psi.toMonoidHom.comp (FreeGroup.lift ι)) := by
    rw [hright]
  have hleft :=
    congrArg
      (fun ρ : FreeGroup X →* K =>
        FoxDifferential.zcFreeGroupFoxDerivativeVector C ρ w)
      hcoeff.symm
  exact hleft.trans (by
    simpa [freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger,
      X, ι, hfree, φ, hφconv] using hcomp)

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] in
/--
A finite projection of the concrete closed-generated continuous Fox vector gives zero of the
corresponding finite Fox derivative vector for a free-group representative.
-/
theorem foxAlgebraicStageDerivativeVector_eq_zero_of_closedGenFoxVector_proj_eq_zero
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H) (hpsi : Function.Surjective psi)
    (htarget :
      ProCGroups.ProC.HasOpenNormalBasisInClass C
        (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (C := C)
          (fun i : ULift.{u} (Fin r) =>
            psi (freeProCChosenULiftFamilyOfBasisCard
              (C := C) sourceData hbasis i)) : Subgroup
            (FoxDifferential.ZCCompletedFoxSemidirect
              C (ULift.{u} (Fin r)) H)))
    (N : Subgroup (FreeGroup (ULift.{u} (Fin r)))) [N.Normal]
    [TopologicalSpace (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)]
    [IsTopologicalGroup (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)]
    [DiscreteTopology (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)]
    (hCN : C
      (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N))
    (η : H →ₜ* FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)
    (hη :
      (η : H →* FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N).comp
          ((psi : sourceData.carrier →* H).comp
            (FreeGroup.lift
              (freeProCChosenULiftFamilyOfBasisCard
                (C := C) sourceData hbasis))) =
        QuotientGroup.mk' N)
    (j : ProCGroups.Completion.ProCIntegerIndex C)
    {w : FreeGroup (ULift.{u} (Fin r))}
    (hproj :
      (fun i : ULift.{u} (Fin r) =>
        FoxDifferential.zcCompletedGroupAlgebraProjection C
          (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)
          (j, FoxDifferential.identityCompletedGroupAlgebraIndexInClassOfMem
            C
            (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)
            hIso hCN)
          ((FoxDifferential.zcFreeFoxCoordinatesMap
            (X := ULift.{u} (Fin r)) C hC η
            (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
              (H := H) (C := C) sourceData hbasis psi htarget
              ((FreeGroup.lift
                (freeProCChosenULiftFamilyOfBasisCard
                  (C := C) sourceData hbasis)) w))) i)) = 0) :
    FoxDifferential.foxAlgebraicStageDerivativeVector
        (X := ULift.{u} (Fin r)) N j.modulus w = 0 := by
  have hcompare :=
    freeFoxDerivVec_eq_freeProCClosedGenFoxVectorZC_comp_lift_mapTarget
      (H := H) (C := C) hForm hC sourceData hbasis psi hpsi htarget η w
  have hcompare' :
      FoxDifferential.zcFreeGroupFoxDerivativeVector C
          (QuotientGroup.mk' N) w =
        FoxDifferential.zcFreeFoxCoordinatesMap
          (X := ULift.{u} (Fin r)) C hC η
          (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
            (H := H) (C := C) sourceData hbasis psi htarget
            ((FreeGroup.lift
              (freeProCChosenULiftFamilyOfBasisCard
                (C := C) sourceData hbasis)) w)) := by
    exact
      (congrArg
        (fun ρ : FreeGroup (ULift.{u} (Fin r)) →*
            FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N =>
          FoxDifferential.zcFreeGroupFoxDerivativeVector C ρ w)
        hη).symm.trans hcompare
  have hproj' :
      (fun i : ULift.{u} (Fin r) =>
        FoxDifferential.zcCompletedGroupAlgebraProjection C
          (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)
          (j, FoxDifferential.identityCompletedGroupAlgebraIndexInClassOfMem
            C
            (FoxDifferential.zcFiniteStageTarget (ULift.{u} (Fin r)) N)
            hIso hCN)
          (FoxDifferential.zcFreeGroupFoxDerivativeVector C
            (QuotientGroup.mk' N) w i)) = 0 := by
    simpa [hcompare'] using hproj
  exact
    foxAlgebraicStageDerivativeVector_eq_zero_of_zcFreeFoxDerivVec_identityProj_eq_zero
      (C := C) (X := ULift.{u} (Fin r)) N hIso hCN j hproj'

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] in
/--
Local constancy of a finite target/coefficent projection of the concrete closed-generated
continuous Fox vector.
-/
theorem exists_openNormalSubgroupInClass_eq_on_right_coset_closedGenFoxVector_proj
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (htarget :
      ProCGroups.ProC.HasOpenNormalBasisInClass C
        (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (C := C)
          (fun i : ULift.{u} (Fin r) =>
            psi (freeProCChosenULiftFamilyOfBasisCard
              (C := C) sourceData hbasis i)) : Subgroup
            (FoxDifferential.ZCCompletedFoxSemidirect
              C (ULift.{u} (Fin r)) H)))
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (η : H →ₜ* K)
    (j : FoxDifferential.ZCCompletedGroupAlgebraIndex C K)
    (g₀ : sourceData.carrier) :
    ∃ U : OpenNormalSubgroupInClass C sourceData.carrier,
      ∀ g : sourceData.carrier,
        g * g₀⁻¹ ∈ (U.1 : Subgroup sourceData.carrier) →
          (fun i : ULift.{u} (Fin r) =>
            FoxDifferential.zcCompletedGroupAlgebraProjection C K j
              ((FoxDifferential.zcFreeFoxCoordinatesMap
                (X := ULift.{u} (Fin r)) C hC η
                (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
                  (H := H) (C := C) sourceData hbasis psi htarget g)) i)) =
          (fun i : ULift.{u} (Fin r) =>
            FoxDifferential.zcCompletedGroupAlgebraProjection C K j
              ((FoxDifferential.zcFreeFoxCoordinatesMap
                (X := ULift.{u} (Fin r)) C hC η
                (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
                  (H := H) (C := C) sourceData hbasis psi htarget g₀)) i)) := by
  let f : sourceData.carrier →
      (ULift.{u} (Fin r) →
        FoxDifferential.ZCCompletedGroupAlgebraStage C K j) :=
    fun g i =>
      FoxDifferential.zcCompletedGroupAlgebraProjection C K j
        ((FoxDifferential.zcFreeFoxCoordinatesMap
          (X := ULift.{u} (Fin r)) C hC η
          (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
            (H := H) (C := C) sourceData hbasis psi htarget g)) i)
  have hf : Continuous f := by
    have hD :
        Continuous
          (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
            (H := H) (C := C) sourceData hbasis psi htarget) :=
      continuous_freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
        (H := H) (C := C) sourceData hbasis psi htarget
    have hmap :
        Continuous (fun g : sourceData.carrier =>
          FoxDifferential.zcFreeFoxCoordinatesMap
            (X := ULift.{u} (Fin r)) C hC η
            (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
              (H := H) (C := C) sourceData hbasis psi htarget g)) :=
      (FoxDifferential.continuous_zcFreeFoxCoordinatesMap
        C hC η).comp hD
    refine continuous_pi fun i => ?_
    change Continuous (fun g : sourceData.carrier =>
      ((FoxDifferential.zcFreeFoxCoordinatesMap
        (X := ULift.{u} (Fin r)) C hC η
        (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
          (H := H) (C := C) sourceData hbasis psi htarget g)) i).1 j)
    exact (continuous_apply j).comp
      (continuous_subtype_val.comp ((continuous_apply i).comp hmap))
  have hdisc :
      DiscreteTopology
        (ULift.{u} (Fin r) →
          FoxDifferential.ZCCompletedGroupAlgebraStage C K j) := by
    infer_instance
  let :
      DiscreteTopology
        (ULift.{u} (Fin r) →
          FoxDifferential.ZCCompletedGroupAlgebraStage C K j) := hdisc
  simpa [f] using
    exists_openNormalSubgroupInClass_eq_on_right_coset_of_continuous_discrete
      (C := C) sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass f hf g₀

end ProfiniteTarget

end

end CrowellExactSequence
