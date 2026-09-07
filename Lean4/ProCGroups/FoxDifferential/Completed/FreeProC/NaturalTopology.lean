import ProCGroups.FreeProC.FiniteBasis
import ProCGroups.FoxDifferential.Completed.Continuous.Magnus.ClosedGeneratedVector
import ProCGroups.FoxDifferential.Completed.Continuous.ClosedGeneratedCoordinates.Topology
import ProCGroups.FoxDifferential.Completed.FreeProC.RelationReflection

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — natural topology

The principal declarations in this module are:

- `freeProCClosedGeneratedTarget_proC_of_surjective`
  For a surjective map from a free pro-\(C\) group, the closed-generated target is again pro-\(C\).
- `freeProC_zcDiffModuleStageProjsSeparate_of_finiteRelationReductionsReflectRelations`
  Free pro-\(C\) finite-stage separation of \(A_{\psi}(C)\), reduced to the relation-reflection form
  of the finite source, target, and coefficient reductions. The remaining mathematical content is
  precisely the reflection hypothesis.
- `freeProC_t2Space_zcDiffModuleNaturalTopology_of_finiteRelationReductionsReflectRelations`
  Free pro-\(C\) Hausdorffness of the finite-stage completed topology on \(A_{\psi}(C)\), reduced to
  the relation-reflection form of finite-stage separation.
- `freeProC_zcDiffModuleStageProjsSeparate_of_relSubmoduleClosed`
  Closedness of the completed relation submodule implies that finite-stage projections separate
  points of the completed differential module.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential
open ProCGroups.ProC

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {C : ProCGroups.FiniteGroupClass.{u}}

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] in
/--
For a surjective map from a free pro-\(C\) group, the closed-generated target is again
pro-\(C\).
-/
theorem freeProCClosedGeneratedTarget_proC_of_surjective
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    HasOpenNormalBasisInClass C
      (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (C := C)
        (fun i : ULift.{u} (Fin r) =>
          psi (freeProCChosenULiftFamilyOfBasisCard
            (C := C) sourceData hbasis i)) : Subgroup
          (ZCCompletedFoxSemidirect C (ULift.{u} (Fin r)) H)) := by
  let family : ULift.{u} (Fin r) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis
  have hH : HasOpenNormalBasisInClass C H :=
    HasOpenNormalBasisInClass.of_surjective
      hC.melnikovFormation.formation
      sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass psi hpsi
  have hAmbient :
      HasOpenNormalBasisInClass C
        (ZCCompletedFoxSemidirect C (ULift.{u} (Fin r)) H) :=
    FoxDifferential.hasOpenNormalBasisInClass_zcCompletedFoxSemidirect_of_hasOpenNormalBasisInClass
      (C := C) (X := ULift.{u} (Fin r)) (H := H)
      hC.melnikovFormation hH
  simpa [family] using
    FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget_hasOpenNormalBasisInClass
      (C := C) hC.melnikovFormation.formation
      hC.hereditary hAmbient
      (fun i : ULift.{u} (Fin r) => psi (family i))

omit [C.ContainsTrivialQuotients] in
/--
Free pro-\(C\) finite-stage separation of \(A_{\psi}(C)\), reduced to the relation-reflection
form of the finite source, target, and coefficient reductions. The remaining mathematical
content is precisely the reflection hypothesis.
-/
theorem freeProC_zcDiffModuleStageProjsSeparate_of_finiteRelationReductionsReflectRelations
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hreflect :
      zcCompletedDifferentialModuleFiniteRelationReductionsReflectRelations
        C psi.toMonoidHom) :
    zcCompletedDifferentialModuleStageProjectionsSeparate
      C psi.toMonoidHom :=
  zcDiffModuleStageProjsSeparate_of_preStageProjsSeparate
    C psi.toMonoidHom
    ((zcDiffModulePreStageProjsSeparate_iff_finiteRelationReductionsReflectRelations
      (C := C) (ψ := psi.toMonoidHom)).2 hreflect)

omit [C.ContainsTrivialQuotients] in
/--
Free pro-\(C\) Hausdorffness of the finite-stage completed topology on \(A_{\psi}(C)\), reduced
to the relation-reflection form of finite-stage separation.
-/
theorem freeProC_t2Space_zcDiffModuleNaturalTopology_of_finiteRelationReductionsReflectRelations
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hreflect :
      zcCompletedDifferentialModuleFiniteRelationReductionsReflectRelations
        C psi.toMonoidHom) :
    @T2Space
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      (zcCompletedDifferentialModuleNaturalTopology
        C psi.toMonoidHom) :=
  t2Space_zcCompletedDifferentialModuleNaturalTopology_of_separating
    C psi.toMonoidHom
    (freeProC_zcDiffModuleStageProjsSeparate_of_finiteRelationReductionsReflectRelations
      (H := H) (C := C) sourceData psi hreflect)

/--
Closedness of the completed relation submodule implies that finite-stage projections separate
points of the completed differential module.
-/
theorem freeProC_zcDiffModuleStageProjsSeparate_of_relSubmoduleClosed
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hclosed :
      zcCompletedDifferentialModuleRelationSubmoduleClosed
        C psi.toMonoidHom) :
    zcCompletedDifferentialModuleStageProjectionsSeparate
      C psi.toMonoidHom := by
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
  exact
    freeProC_zcDiffModuleStageProjsSeparate_of_finiteRelationReductionsReflectRelations
      (H := H) (C := C) sourceData psi
      (zcDiffModuleFiniteRelationReductionsReflectRelations_of_relSubmoduleClosed
        C psi.toMonoidHom hdir hclosed)

/--
Closedness of the completed relation submodule makes the natural topology on the completed
differential module Hausdorff.
-/
theorem freeProC_t2Space_zcDiffModuleNaturalTopology_of_relSubmoduleClosed
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hclosed :
      zcCompletedDifferentialModuleRelationSubmoduleClosed
        C psi.toMonoidHom) :
    @T2Space
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      (zcCompletedDifferentialModuleNaturalTopology
        C psi.toMonoidHom) :=
  t2Space_zcCompletedDifferentialModuleNaturalTopology_of_separating
    C psi.toMonoidHom
    (freeProC_zcDiffModuleStageProjsSeparate_of_relSubmoduleClosed
      (H := H) (C := C) (hC := hC) sourceData psi hclosed)

/--
Closedness of the completed relation submodule is equivalent to separation by all finite-stage
projections.
-/
theorem freeProC_zcDiffModuleRelSubmoduleClosed_iff_stageProjsSeparate
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    {sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C}
    {psi : ContinuousMonoidHom sourceData.carrier H} :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
        C psi.toMonoidHom ↔
      zcCompletedDifferentialModuleStageProjectionsSeparate
        C psi.toMonoidHom := by
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
  exact
    zcDiffModuleRelSubmoduleClosed_iff_stageProjsSeparate
      (C := C) (ψ := psi.toMonoidHom) hdir

/--
Closedness of the completed relation submodule is equivalent to the natural topology being
Hausdorff.
-/
theorem freeProC_zcDiffModuleRelSubmoduleClosed_iff_t2_naturalTopology
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    {sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C}
    {psi : ContinuousMonoidHom sourceData.carrier H} :
    zcCompletedDifferentialModuleRelationSubmoduleClosed
        C psi.toMonoidHom ↔
      @T2Space
        (ZCCompletedDifferentialModule C psi.toMonoidHom)
        (zcCompletedDifferentialModuleNaturalTopology
          C psi.toMonoidHom) := by
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
  exact
    zcCompletedDifferentialModuleRelationSubmoduleClosed_iff_t2_naturalTopology
      (C := C) (ψ := psi.toMonoidHom) hdir

omit [C.ContainsTrivialQuotients] in
/--
For a finite free pro-\(C\) basis and a surjective presentation, the completed differential-module
map is continuous for its natural topology.
-/
theorem freeProC_hmodule_continuous_naturalTopology
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    @Continuous sourceData.carrier
      (ZCCompletedDifferentialModule C psi.toMonoidHom)
      inferInstance
      (zcCompletedDifferentialModuleNaturalTopology
        C psi.toMonoidHom)
      (fun g : sourceData.carrier =>
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
            g)) := by
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
  simpa [family, hfree, htarget, hφconv] using
    continuous_closedGenerated_module_expansion_naturalTopology
      (G := sourceData.carrier) (H := H) C psi family hfree htarget hφconv

end

end CrowellExactSequence
