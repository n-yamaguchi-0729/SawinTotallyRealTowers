/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Magnus.KernelClosedCommutator
import Nyll.ProCGroups.CrowellExactSequence.Profinite.KernelInjectivity

/-!
# Crowell Exact Sequence / Profinite / Continuous Magnus / Injectivity

This module proves injectivity of the completed Magnus map on the
abelianized presentation kernel, using the closed-commutator kernel
calculation and the general kernel-injectivity criterion.
-/

namespace CrowellExactSequence

noncomputable section

open ProCGroups.ProC

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {C : ProCGroups.FiniteGroupClass.{u}}

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] in
/--
Continuous Magnus injectivity for the displayed boundary \(d_N\): \(N^{\mathrm{ab}}(C)\)
\(\to\) \(A_{\psi}(C)\). This step is obtained by combining the completed Fox-vector kernel
theorem with the general kernel criterion for the topological kernel abelianization.
-/
theorem freeProC_profKerAbBoundaryAddZC_inj_of_continuousMagnus
    [CompactSpace H]
    [T2Space H]
    [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H) (hpsi : Function.Surjective psi)
    (htarget :
      HasOpenNormalBasisInClass C
        (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (C := C)
          (fun i : ULift.{u} (Fin r) =>
            psi (freeProCChosenULiftFamilyOfBasisCard
              (C := C) sourceData hbasis i)) : Subgroup
            (FoxDifferential.ZCCompletedFoxSemidirect
              C (ULift.{u} (Fin r)) H)))
    (hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger
        (G := sourceData.carrier) (H := H) C psi) :
    Function.Injective
      (profiniteKernelAbelianizationBoundaryAddProCInteger
        (G := sourceData.carrier) (H := H) C psi hwell_dN) :=
  profKerAbBoundaryAddZC_inj_of_kernel_le_closedCommutator
    (G := sourceData.carrier) (H := H) C psi hwell_dN
    (freeProC_zcUnivDiff_kernel_le_closedCommutator_of_closedGenFoxVector
      (H := H) (C := C) hC.melnikovFormation.formation
      sourceData hbasis psi hpsi htarget
      (freeProC_closedGeneratedFoxVector_kernel_le_closedCommutator
        (H := H) (C := C) hC sourceData hbasis psi hpsi htarget))


end

end CrowellExactSequence
