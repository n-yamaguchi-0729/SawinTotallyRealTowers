/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CrowellExactSequence.Profinite.BlanchfieldLyndon
import Nyll.ProCGroups.FreeProC.FiniteRankSourceData
import Nyll.ProCGroups.FiniteStepSolvableQuotients.Abelianization
import Nyll.ProCGroups.ProC.InverseLimits.Predicates

/-!
# `ProCGroups.CrowellExactSequence.Applications.FiniteRank`

Crowell exact sequences / Applications / Finite Rank.

This module develops the Crowell--Blanchfield--Lyndon exact sequence and its completed
coordinate forms.
-/

open scoped Topology

namespace CrowellExactSequence

open ProCGroups.Abelian
open ProCGroups.FiniteStepSolvableQuotients

universe u

variable {F : Type u} [TopologicalSpace F] [Group F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]

/--
The separated coordinate map for the topological abelianization of a finite-rank free
pro-\(\Sigma\) group.
-/
noncomputable def finiteRank_topologicalAbelianization_sepCoordinateMap
    {sigma : Set ℕ} {r : ℕ} (X : Fin r → F)
    (hFree : ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := (ProCGroups.FiniteGroupClass.sigmaGroup.{u} sigma))
      (Fin r) F X) := by
  letI :
      ProCGroups.FiniteGroupClass.ContainsTrivialQuotients
        (ProCGroups.FiniteGroupClass.sigmaGroup sigma) :=
    (ProCGroups.FiniteGroupClass.sigmaGroup_fullFormation sigma).containsTrivialQuotients
  letI : TotallyDisconnectedSpace (TopologicalAbelianization F) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator F) (Subgroup.isClosed_closedCommutator F)
  exact
    freeProCChosenULift_sepCoordinateMap
      (H := TopologicalAbelianization F)
      (C := ProCGroups.FiniteGroupClass.sigmaGroup sigma)
      (ProCGroups.FiniteGroupClass.sigmaGroup_fullFormation sigma)
      (finiteRank_epimorphicallyFreeProCSourceData (F := F) X hFree)
      (finiteRank_epimorphicallyFreeProCSourceData_basis_card (F := F) X hFree)
      (TopologicalAbelianization.mkₜ F)
      (by
        change Function.Surjective (TopologicalAbelianization.mk F)
        exact TopologicalAbelianization.surjective_mk F)

/--
If the separated abelianized Crowell exact-sequence coordinate vector of a kernel element
vanishes, the element lies in the second closed derived subgroup.
-/
theorem mem_topDerivedTop_two_of_finiteRank_topologicalAbelianization_sepCoordinateMap_eq_zero
    {sigma : Set ℕ} {r : ℕ} (X : Fin r → F)
    (hFree : ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := (ProCGroups.FiniteGroupClass.sigmaGroup.{u} sigma))
      (Fin r) F X)
    {a : F}
    (haψ : TopologicalAbelianization.mkₜ F a = 1)
    (hzero :
      finiteRank_topologicalAbelianization_sepCoordinateMap (F := F) X hFree
        (FoxDifferential.zcSeparatedUniversalDifferential
          (ProCGroups.FiniteGroupClass.sigmaGroup sigma)
          (TopologicalAbelianization.mkₜ F).toMonoidHom a) = 0) :
    a ∈ topDerivedTop F 2 := by
  let :
      ProCGroups.FiniteGroupClass.ContainsTrivialQuotients
        (ProCGroups.FiniteGroupClass.sigmaGroup sigma) :=
    (ProCGroups.FiniteGroupClass.sigmaGroup_fullFormation sigma).containsTrivialQuotients
  let : TotallyDisconnectedSpace (TopologicalAbelianization F) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator F) (Subgroup.isClosed_closedCommutator F)
  let sourceData := finiteRank_epimorphicallyFreeProCSourceData (F := F) (sigma := sigma) X hFree
  let hbasis := finiteRank_epimorphicallyFreeProCSourceData_basis_card (F := F) X hFree
  let C := ProCGroups.FiniteGroupClass.sigmaGroup sigma
  let ψ : F →ₜ* TopologicalAbelianization F := TopologicalAbelianization.mkₜ F
  have hψsurj : Function.Surjective ψ := by
    change Function.Surjective (TopologicalAbelianization.mk F)
    exact TopologicalAbelianization.surjective_mk F
  let htarget :=
    freeProCClosedGeneratedTarget_proC_of_surjective
      (H := TopologicalAbelianization F) (C := C)
      (ProCGroups.FiniteGroupClass.sigmaGroup_fullFormation sigma)
      sourceData hbasis ψ hψsurj
  have hDzero :
      freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
        (H := TopologicalAbelianization F) (C := C) sourceData hbasis ψ htarget a = 0 := by
    have happly := hzero
    dsimp [finiteRank_topologicalAbelianization_sepCoordinateMap, sourceData, hbasis,
      C, ψ] at happly
    change
      freeProCChosenULift_sepCoordinateMap
          (H := TopologicalAbelianization F) (C := C)
          (ProCGroups.FiniteGroupClass.sigmaGroup_fullFormation sigma)
          sourceData hbasis ψ hψsurj
          (FoxDifferential.zcSeparatedUniversalDifferential C
            ψ.toMonoidHom a) = 0 at happly
    have hcoord :=
      freeProCChosenULift_sepCoordinateMap_universal
        (H := TopologicalAbelianization F) (C := C)
        (hC := ProCGroups.FiniteGroupClass.sigmaGroup_fullFormation sigma)
        sourceData hbasis ψ hψsurj a
    have hraw := hcoord.symm.trans happly
    simpa [finiteRank_topologicalAbelianization_sepCoordinateMap, sourceData, hbasis, C, ψ,
      freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger, htarget] using hraw
  have ha_closed :
      (⟨a, haψ⟩ : ProCGroups.ProC.ProfiniteKernelSubgroup ψ) ∈
        Subgroup.closedCommutator (ProCGroups.ProC.ProfiniteKernelSubgroup ψ) :=
    freeProC_closedGeneratedFoxVector_kernel_le_closedCommutator
      (H := TopologicalAbelianization F) (C := C)
      (ProCGroups.FiniteGroupClass.sigmaGroup_fullFormation sigma)
      sourceData hbasis ψ hψsurj htarget
      ⟨a, haψ⟩ hDzero
  exact
    (mem_topDerivedTop_two_iff_mem_closedCommutator_topologicalAbelianizationKernel
      (G := F) haψ).2 ha_closed

end CrowellExactSequence
