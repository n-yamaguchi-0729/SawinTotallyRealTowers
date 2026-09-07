import ProCGroups.FreeProC.FiniteBasis
import ProCGroups.FoxDifferential.Completed.Continuous.Free.Continuity
import ProCGroups.FoxDifferential.Completed.Continuous.TopologicalGeneration

set_option autoImplicit false

/-!
# Fox Differential / Completed / Continuous Magnus / Closed Generated Vector

This module bundles the completed Fox derivative vector as a scalar crossed
homomorphism, first over pro-\(C\) integers and then over the presented
coefficient ring.  It also records the closed-generation and Magnus-reduction
identities used by the completed Magnus injectivity argument.
-/

namespace CrowellExactSequence

noncomputable section

open ProCGroups.ProC
open FoxDifferential

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {C : ProCGroups.FiniteGroupClass.{u}}

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]

section ProfiniteTarget

variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/--
The closed-generated continuous Fox derivative vector attached to a finite chosen free
pro-\(C\) basis and a presentation map.
-/
def freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
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
              C (ULift.{u} (Fin r)) H))) :
    FoxDifferential.ScalarCrossedHom
      (FoxDifferential.zcCompletedGroupAlgebraScalar C
        (FoxDifferential.freeProCZCCompletedFoxRightHomViaClosedGenerated
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
                (C := C) sourceData hbasis i)))))
      (FoxDifferential.ZCFreeFoxCoordinates
        C (X := ULift.{u} (Fin r)) (H := H)) :=
  let hfree :=
    freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis
  let φ : ULift.{u} (Fin r) → H := fun i =>
    psi (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis i)
  let hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (C := C) φ : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect
                C (ULift.{u} (Fin r)) H)))
        (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
          (C := C) φ) :=
    FoxDifferential.freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
      (C := C) φ
  FoxDifferential.freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
    (C := C) hfree φ htarget hφconv

end ProfiniteTarget

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] in
/--
An abstract kernel word for the chosen finite free basis gives a genuine cycle point in the
closed-generated Fox graph target. This is the algebraic source of the completed cycle-lifting
step: before passing to closures, every relation word \(w\) with target value \(1\) contributes
\((D w, 1)\) to the closed-generated graph.
-/
theorem freeProC_closedGeneratedTarget_mem_of_freeGroupFoxDerivativeVector_kernel
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    {w : FreeGroup (ULift.{u} (Fin r))}
    (hw :
      FreeGroup.lift
          (fun i : ULift.{u} (Fin r) =>
            psi (freeProCChosenULiftFamilyOfBasisCard
              (C := C) sourceData hbasis i)) w = 1) :
    ({ left :=
        FoxDifferential.zcFreeGroupFoxDerivativeVector C
          (FreeGroup.lift
            (fun i : ULift.{u} (Fin r) =>
              psi (freeProCChosenULiftFamilyOfBasisCard
                (C := C) sourceData hbasis i))) w,
       right := (1 : H) } :
      FoxDifferential.ZCCompletedFoxSemidirect C
        (ULift.{u} (Fin r)) H) ∈
      (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (C := C)
        (fun i : ULift.{u} (Fin r) =>
          psi (freeProCChosenULiftFamilyOfBasisCard
            (C := C) sourceData hbasis i)) : Subgroup
          (FoxDifferential.ZCCompletedFoxSemidirect C
            (ULift.{u} (Fin r)) H)) := by
  exact
    FoxDifferential.freeProCZCFoxClosedGenTarget_mem_of_freeFoxDerivVec_kernel
      (C := C)
      (fun i : ULift.{u} (Fin r) =>
        psi (freeProCChosenULiftFamilyOfBasisCard
          (C := C) sourceData hbasis i))
      hw

section ProfiniteTarget

variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] in
/--
The right component of the closed-generated Fox graph attached to the chosen lifted finite
basis is the original presentation map; the two continuous homomorphisms agree on every chosen
free generator.
-/
theorem freeProCCompletedFoxRightHomViaClosedGeneratedProCInteger_eq
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
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
              C (ULift.{u} (Fin r)) H))) :
    FoxDifferential.freeProCZCCompletedFoxRightHomViaClosedGenerated
        (C := C)
        (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis)
        (fun i : ULift.{u} (Fin r) =>
          psi (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis i))
        htarget
        (freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
          (C := C)
          (fun i : ULift.{u} (Fin r) =>
            psi (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis i))) =
      psi.toMonoidHom := by
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
  have hH : ProCGroups.ProC.HasOpenNormalBasisInClass C H :=
    ProCGroups.ProC.HasOpenNormalBasisInClass.of_surjective
      hForm sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass psi hpsi
  have hφHconv : ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups (G := H) φ := by
    simpa [φ, ι] using
      freeProCChosenULiftFamilyOfBasisCard_image_convergesToOneAlongOpenSubgroups
        (C := C) sourceData hbasis psi.toMonoidHom
  have hφHgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ) := by
    simpa [φ, ι] using
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (C := C) sourceData hbasis psi hpsi
  simpa [X, ι, hfree, φ, hφconv] using
    FoxDifferential.freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
      (C := C) X H hfree hH φ htarget hφconv hφHconv hφHgen psi
      (by intro i; rfl)

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] in
/-- The closed-generated continuous Fox derivative vector, bundled with the
original presentation map as its coefficient homomorphism. -/
def freeProCCompletedFoxDerivativeVectorForPresentation
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
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
              C (ULift.{u} (Fin r)) H))) :
    FoxDifferential.ScalarCrossedHom
      (FoxDifferential.zcCompletedGroupAlgebraScalar
        C psi.toMonoidHom)
      (FoxDifferential.ZCFreeFoxCoordinates
        C (X := ULift.{u} (Fin r)) (H := H)) where
  toFun :=
    freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
      (H := H) (C := C) sourceData hbasis psi htarget
  map_mul' := by
    intro g h
    let X : Type u := ULift.{u} (Fin r)
    let ι : X → sourceData.carrier :=
      freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis
    let hfree :=
      freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree
        (C := C) sourceData hbasis
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
    have hright :
        FoxDifferential.freeProCZCCompletedFoxRightHomViaClosedGenerated
            (C := C) hfree φ htarget hφconv =
          psi.toMonoidHom := by
      simpa [X, ι, hfree, φ, hφconv] using
        freeProCCompletedFoxRightHomViaClosedGeneratedProCInteger_eq
          (H := H) (C := C) hForm sourceData hbasis psi hpsi htarget
    have hD :=
      (FoxDifferential.freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
        (C := C) hfree φ htarget hφconv).map_mul g h
    rw [← hright]
    exact hD

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] in
/-- The closed-generated continuous Fox derivative vector is continuous. -/
theorem continuous_freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
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
              C (ULift.{u} (Fin r)) H))) :
    Continuous
      (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
        (H := H) (C := C) sourceData hbasis psi htarget) := by
  let hfree :=
    freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis
  let φ : ULift.{u} (Fin r) → H := fun i =>
    psi (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis i)
  let hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (C := C) φ : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect
                C (ULift.{u} (Fin r)) H)))
        (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
          (C := C) φ) :=
    FoxDifferential.freeProCZCFoxSemiClosedGenGenerator_convergesToOneAlongOpenSubgroups_of_finite
      (C := C) φ
  simpa [freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger, hfree, φ, hφconv] using
    FoxDifferential.continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
      (C := C) (ULift.{u} (Fin r)) H hfree φ htarget hφconv

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] in
/--
Universal completed Magnus-kernel reduction for the closed-generated continuous Fox vector.
After this reduction, the remaining paper statement is exactly the concrete continuous Magnus
kernel for the completed Fox derivative vector.
-/
theorem freeProC_zcUnivDiff_kernel_le_closedCommutator_of_closedGenFoxVector
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
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
    (hDker :
      ∀ n : ProfiniteKernelSubgroup psi,
        freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
            (H := H) (C := C) sourceData hbasis psi htarget n.1 = 0 →
          n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup psi)) :
    ∀ n : ProfiniteKernelSubgroup psi,
      FoxDifferential.zcUniversalDifferential
          C psi.toMonoidHom n.1 = 0 →
        n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup psi) := by
  exact
    FoxDifferential.zcUniversalDifferential_kernel_le_closedCommutator_of_crossedDifferential
      C psi
      (freeProCCompletedFoxDerivativeVectorForPresentation
        (H := H) (C := C) hForm sourceData hbasis psi hpsi htarget)
      hDker

end ProfiniteTarget

end

end CrowellExactSequence
