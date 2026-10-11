/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Free.Rules

/-!
# Fox differential: completed — continuous — chain rule — basic

The principal declarations in this module are:

- `allFinite_freeProCZCCompletedFoxPullbackGenerator`
  The target generator map pulled back along a continuous homomorphism of free pro-\(C\) sources.
- `allFinite_freeProCZCCompletedFoxJacobian`
  The completed Fox-Jacobian family of a continuous homomorphism between free pro-\(C\) sources.
- `allFinite_freeProCZCCompletedFoxJacobianMatrix_apply`
  The matrix evaluation is componentwise the completed Fox-Jacobian family.
- `allFinite_freeProCZCCompletedFoxJacobianMatrixStage_apply`
  Evaluation of the finite-stage completed Fox-Jacobian matrix.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v

section AllFiniteChainRule

variable {X Y F F' H : Type u}
variable [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
variable [DecidableEq Y] [TopologicalSpace Y] [DiscreteTopology Y]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable [CompactSpace F'] [T2Space F'] [TotallyDisconnectedSpace F']
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/--
The target generator map pulled back along a continuous homomorphism of free pro-\(C\) sources.
-/
def allFinite_freeProCZCCompletedFoxPullbackGenerator
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F) : X → H :=
  fun x =>
    freeProCZCCompletedFoxRightHom
      (C := ProCGroups.FiniteGroupClass.allFinite) hκ
      (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
      (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
          ProCGroups.FiniteGroupClass.allFinite) Y H φ)
      (η (ι x))

/--
The completed Fox-Jacobian family of a continuous homomorphism between free pro-\(C\) sources.
-/
def allFinite_freeProCZCCompletedFoxJacobian
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F) :
    X → ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := Y) (H := H) :=
  fun x =>
    freeProCZCCompletedFoxDerivativeVector
      (C := ProCGroups.FiniteGroupClass.allFinite) hκ
      (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
      (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
          ProCGroups.FiniteGroupClass.allFinite) Y H φ)
      (η (ι x))

/--
The completed Fox-Jacobian family is bundled into a finite linear map on completed coordinate
vectors.
-/
def allFinite_freeProCZCCompletedFoxJacobianLinearMap
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F) :
    ZCFreeFoxCoordinates
        ProCGroups.FiniteGroupClass.allFinite (X := X) (H := H) →ₗ[
          ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H]
      ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := Y) (H := H) :=
  foxJacobianLinearMap
    (allFinite_freeProCZCCompletedFoxJacobian (X := X) (F := F) hκ η φ ι)

/-- The completed Fox-Jacobian is packaged as a matrix. -/
def allFinite_freeProCZCCompletedFoxJacobianMatrix
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F) :
    Matrix X Y (ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H) :=
  foxJacobianMatrix
    (allFinite_freeProCZCCompletedFoxJacobian (X := X) (F := F) hκ η φ ι)

/-- A finite-stage projection of the completed Fox-Jacobian matrix. -/
def allFinite_freeProCZCCompletedFoxJacobianMatrixStage
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F)
    (j : ZCCompletedGroupAlgebraIndex ProCGroups.FiniteGroupClass.allFinite H) :
    Matrix X Y (ZCCompletedGroupAlgebraStage ProCGroups.FiniteGroupClass.allFinite H j) :=
  fun x y =>
    zcCompletedGroupAlgebraProjection ProCGroups.FiniteGroupClass.allFinite H j
      (allFinite_freeProCZCCompletedFoxJacobianMatrix
        (X := X) (F := F) hκ η φ ι x y)

omit [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [IsTopologicalGroup F] in
/-- The matrix evaluation is componentwise the completed Fox-Jacobian family. -/
@[simp]
theorem allFinite_freeProCZCCompletedFoxJacobianMatrix_apply
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F)
    (x : X) (y : Y) :
    allFinite_freeProCZCCompletedFoxJacobianMatrix
        (X := X) (F := F) hκ η φ ι x y =
      allFinite_freeProCZCCompletedFoxJacobian
        (X := X) (F := F) hκ η φ ι x y :=
  rfl

omit [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [IsTopologicalGroup F] in
/-- Evaluation of the finite-stage completed Fox-Jacobian matrix. -/
@[simp]
theorem allFinite_freeProCZCCompletedFoxJacobianMatrixStage_apply
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F)
    (j : ZCCompletedGroupAlgebraIndex ProCGroups.FiniteGroupClass.allFinite H) (x : X) (y : Y) :
    allFinite_freeProCZCCompletedFoxJacobianMatrixStage
        (X := X) (F := F) hκ η φ ι j x y =
      zcCompletedGroupAlgebraProjection ProCGroups.FiniteGroupClass.allFinite H j
        (allFinite_freeProCZCCompletedFoxJacobianMatrix
          (X := X) (F := F) hκ η φ ι x y) :=
  rfl

omit [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [IsTopologicalGroup F] in
/--
The all-finite pro-\(C\) completed Fox-Jacobian linear map is evaluated coordinatewise at each
finite quotient stage.
-/
@[simp]
theorem allFinite_freeProCZCCompletedFoxJacobianLinearMap_apply
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F)
    (v : ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := X) (H := H)) (y : Y) :
    allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (F := F) hκ η φ ι v y =
      ∑ x : X,
        v x * allFinite_freeProCZCCompletedFoxJacobian
          (X := X) (F := F) hκ η φ ι x y :=
  rfl

omit [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [IsTopologicalGroup F] in
/-- The completed Fox-Jacobian linear map is row-vector multiplication by its matrix. -/
theorem allFinite_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul
    {κ : Y → F'}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →* F') (φ : Y → H) (ι : X → F)
    (v : ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := X) (H := H)) :
    allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (F := F) hκ η φ ι v =
      Matrix.vecMul v
        (allFinite_freeProCZCCompletedFoxJacobianMatrix
          (X := X) (F := F) hκ η φ ι) := by
  exact foxJacobianLinearMap_eq_vecMul
    (allFinite_freeProCZCCompletedFoxJacobian (X := X) (F := F) hκ η φ ι) v

omit [Fintype X] in
/--
The canonical right homomorphism for the pulled-back generator map is the composite of the
target right homomorphism with the source homomorphism.
-/
theorem allFinite_freeProCZCCompletedFoxRightHom_comp
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →* F') (hη_continuous : Continuous η) (φ : Y → H) :
    freeProCZCCompletedFoxRightHom
        (C := ProCGroups.FiniteGroupClass.allFinite) hι
        (ProCGrp.allFinite_property (ProfiniteGrp.of _))
        (allFinite_freeProCZCCompletedFoxPullbackGenerator
          (X := X) (F := F) hκ η φ ι)
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) X H
          (allFinite_freeProCZCCompletedFoxPullbackGenerator
            (X := X) (F := F) hκ η φ ι)) =
      (freeProCZCCompletedFoxRightHom
        (C := ProCGroups.FiniteGroupClass.allFinite) hκ
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Y H φ)).comp η := by
  let htargetX :
      ProCGroups.ProC.HasOpenNormalBasisInClass ProCGroups.FiniteGroupClass.allFinite
        (ZCCompletedFoxSemidirect ProCGroups.FiniteGroupClass.allFinite X H) :=
    ProCGrp.allFinite_property (ProfiniteGrp.of _)
  let htargetY :
      ProCGroups.ProC.HasOpenNormalBasisInClass ProCGroups.FiniteGroupClass.allFinite
        (ZCCompletedFoxSemidirect ProCGroups.FiniteGroupClass.allFinite Y H) :=
    ProCGrp.allFinite_property (ProfiniteGrp.of _)
  let hφY : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C :=
      ProCGroups.FiniteGroupClass.allFinite) φ) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
        ProCGroups.FiniteGroupClass.allFinite) Y H φ
  let φX : X → H :=
    allFinite_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hκ η φ ι
  let hφX : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C :=
      ProCGroups.FiniteGroupClass.allFinite) φX) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
        ProCGroups.FiniteGroupClass.allFinite) X H φX
  have hHtarget :
      ProCGroups.ProC.HasOpenNormalBasisInClass ProCGroups.FiniteGroupClass.allFinite H :=
    ProCGrp.allFinite_property (ProfiniteGrp.of H)
  change
    freeProCZCCompletedFoxRightHom
        (C := ProCGroups.FiniteGroupClass.allFinite) hι htargetX φX hφX =
      (freeProCZCCompletedFoxRightHom
        (C := ProCGroups.FiniteGroupClass.allFinite) hκ htargetY φ hφY).comp η
  apply hι.hom_ext hHtarget
  · exact continuous_freeProCZCCompletedFoxRightHom
      (C := ProCGroups.FiniteGroupClass.allFinite) X H hι htargetX φX hφX
  · exact (continuous_freeProCZCCompletedFoxRightHom
      (C := ProCGroups.FiniteGroupClass.allFinite) Y H hκ htargetY φ hφY).comp hη_continuous
  · intro x
    rw [freeProCZCCompletedFoxRightHom_generator]
    rfl

/-- Completed pro-\(C\) Fox chain rule in vector form. -/
theorem allFinite_freeProCZCCompletedFoxDerivativeVector_comp
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →* F') (hη_continuous : Continuous η) (φ : Y → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (C := ProCGroups.FiniteGroupClass.allFinite) hκ
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Y H φ) (η g) =
      allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (F := F) hκ η φ ι
        (freeProCZCCompletedFoxDerivativeVector
          (C := ProCGroups.FiniteGroupClass.allFinite) hι
          (ProCGrp.allFinite_property (ProfiniteGrp.of _))
          (allFinite_freeProCZCCompletedFoxPullbackGenerator
            (X := X) (F := F) hκ η φ ι)
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
              ProCGroups.FiniteGroupClass.allFinite) X H
            (allFinite_freeProCZCCompletedFoxPullbackGenerator
              (X := X) (F := F) hκ η φ ι)) g) := by
  let htargetX :
      ProCGroups.ProC.HasOpenNormalBasisInClass ProCGroups.FiniteGroupClass.allFinite
        (ZCCompletedFoxSemidirect ProCGroups.FiniteGroupClass.allFinite X H) :=
    ProCGrp.allFinite_property (ProfiniteGrp.of _)
  let htargetY :
      ProCGroups.ProC.HasOpenNormalBasisInClass ProCGroups.FiniteGroupClass.allFinite
        (ZCCompletedFoxSemidirect ProCGroups.FiniteGroupClass.allFinite Y H) :=
    ProCGrp.allFinite_property (ProfiniteGrp.of _)
  let hφY : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C :=
      ProCGroups.FiniteGroupClass.allFinite) φ) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
        ProCGroups.FiniteGroupClass.allFinite) Y H φ
  let ρY : F' →* H :=
    freeProCZCCompletedFoxRightHom (C := ProCGroups.FiniteGroupClass.allFinite)
      hκ htargetY φ hφY
  let DY : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar ProCGroups.FiniteGroupClass.allFinite ρY)
      (ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := Y) (H := H)) :=
    freeProCZCCompletedFoxDerivativeVector (C := ProCGroups.FiniteGroupClass.allFinite)
      hκ htargetY φ hφY
  let φX : X → H :=
    allFinite_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hκ η φ ι
  let hφX : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C :=
      ProCGroups.FiniteGroupClass.allFinite) φX) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
        ProCGroups.FiniteGroupClass.allFinite) X H φX
  let ρX : F →* H :=
    freeProCZCCompletedFoxRightHom (C := ProCGroups.FiniteGroupClass.allFinite)
      hι htargetX φX hφX
  let DX : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar ProCGroups.FiniteGroupClass.allFinite ρX)
      (ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := X) (H := H)) :=
    freeProCZCCompletedFoxDerivativeVector (C := ProCGroups.FiniteGroupClass.allFinite)
      hι htargetX φX hφX
  let jac : X → ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := Y) (H := H) :=
    allFinite_freeProCZCCompletedFoxJacobian
      (X := X) (F := F) hκ η φ ι
  let L :
      ZCFreeFoxCoordinates
          ProCGroups.FiniteGroupClass.allFinite (X := X) (H := H) →ₗ[
            ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H]
      ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := Y) (H := H) :=
    allFinite_freeProCZCCompletedFoxJacobianLinearMap
      (X := X) (F := F) hκ η φ ι
  have hρX : ρX = ρY.comp η := by
    simpa [ρX, ρY, φX, htargetX, htargetY, hφX, hφY] using
      allFinite_freeProCZCCompletedFoxRightHom_comp
        (X := X) (Y := Y) (F := F) (F' := F') (H := H) hι hκ η hη_continuous φ
  let beta : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar ProCGroups.FiniteGroupClass.allFinite ρX)
      (ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := Y) (H := H)) := {
    toFun g := DY (η g)
    map_mul' a b := by
      simpa [DY, hρX, map_mul, MonoidHom.comp_apply] using
        ScalarCrossedHom.map_mul DY (η a) (η b) }
  let gamma : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar ProCGroups.FiniteGroupClass.allFinite ρX)
      (ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := Y) (H := H)) :=
    DX.mapLinear L
  have hbeta_continuous : Continuous beta := by
    change Continuous (fun g : F => DY (η g))
    exact (continuous_freeProCZCCompletedFoxDerivativeVector
      (C := ProCGroups.FiniteGroupClass.allFinite) Y H hκ htargetY φ hφY).comp hη_continuous
  have hgamma_continuous : Continuous gamma := by
    refine continuous_pi fun y => ?_
    change Continuous (fun g : F => ∑ x : X, DX g x * jac x y)
    exact continuous_finsetSum _ fun x _ =>
      ((continuous_apply x).comp
        (continuous_freeProCZCCompletedFoxDerivativeVector
          (C := ProCGroups.FiniteGroupClass.allFinite) X H hι htargetX φX hφX)).mul
        continuous_const
  have hgen : ∀ x : X, beta (ι x) = gamma (ι x) := by
    intro x
    have hsingle :
        L ((Pi.single x (1 : ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H)) :
          ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := X) (H := H)) = jac x
              := by
      simp only [allFinite_freeProCZCCompletedFoxJacobianLinearMap, foxJacobianLinearMap_single,
          L, jac]
    change DY (η (ι x)) = L (DX (ι x))
    calc
      DY (η (ι x)) = jac x := by rfl
      _ = L (Pi.single x
          (1 : ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H)) :=
        hsingle.symm
      _ = L (DX (ι x)) := by
        rw [freeProCZCCompletedFoxDerivativeVector_generator
          (C := ProCGroups.FiniteGroupClass.allFinite)
          hι htargetX φX hφX x]
  let f : F →* ZCCompletedFoxSemidirect ProCGroups.FiniteGroupClass.allFinite Y H :=
    freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := Y) (F := F) (H := H) ρX beta
  let h : F →* ZCCompletedFoxSemidirect ProCGroups.FiniteGroupClass.allFinite Y H :=
    freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := Y) (F := F) (H := H) ρX gamma
  have hf_continuous : Continuous f :=
    continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := Y) (F := F) (H := H) ρX beta hbeta_continuous
      (continuous_freeProCZCCompletedFoxRightHom
        (C := ProCGroups.FiniteGroupClass.allFinite) X H hι htargetX φX hφX)
  have hh_continuous : Continuous h :=
    continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := Y) (F := F) (H := H) ρX gamma hgamma_continuous
      (continuous_freeProCZCCompletedFoxRightHom
        (C := ProCGroups.FiniteGroupClass.allFinite) X H hι htargetX φX hφX)
  have hfg : ∀ x : X, f (ι x) = h (ι x) := by
    intro x
    apply ZCCompletedFoxSemidirect.ext
    · exact hgen x
    · rfl
  have hfh : f = h := hι.hom_ext htargetY hf_continuous hh_continuous hfg
  have hleft := congrArg (fun q : F →* ZCCompletedFoxSemidirect
      ProCGroups.FiniteGroupClass.allFinite Y H => (q g).left) hfh
  convert hleft using 1
  all_goals
    simp [f, h, beta, gamma, L, DY, DX, ρY, ρX, φX,
      allFinite_freeProCZCCompletedFoxJacobianLinearMap]
  all_goals rfl

/-- Completed pro-\(C\) Fox chain rule in component form. -/
theorem allFinite_freeProCZCCompletedFoxDerivativeVector_comp_apply
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →* F') (hη_continuous : Continuous η) (φ : Y → H) (g : F) (y : Y) :
    freeProCZCCompletedFoxDerivativeVector
        (C := ProCGroups.FiniteGroupClass.allFinite) hκ
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Y H φ) (η g) y =
      ∑ x : X,
        freeProCZCCompletedFoxDerivativeVector
            (C := ProCGroups.FiniteGroupClass.allFinite) hι
            (ProCGrp.allFinite_property (ProfiniteGrp.of _))
            (allFinite_freeProCZCCompletedFoxPullbackGenerator
              (X := X) (F := F) hκ η φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
                ProCGroups.FiniteGroupClass.allFinite) X H
              (allFinite_freeProCZCCompletedFoxPullbackGenerator
                (X := X) (F := F) hκ η φ ι)) g x *
          allFinite_freeProCZCCompletedFoxJacobian
            (X := X) (F := F) hκ η φ ι x y := by
  have h := congrFun
    (allFinite_freeProCZCCompletedFoxDerivativeVector_comp
      (X := X) (Y := Y) (F := F) (F' := F') (H := H)
      hι hκ η hη_continuous φ g) y
  simpa using h

/-- The completed pro-\(C\) Fox chain rule in matrix form. -/
theorem allFinite_freeProCZCCompletedFoxDerivativeVector_comp_matrix
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →* F') (hη_continuous : Continuous η) (φ : Y → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (C := ProCGroups.FiniteGroupClass.allFinite) hκ
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Y H φ) (η g) =
      Matrix.vecMul
        (freeProCZCCompletedFoxDerivativeVector
          (C := ProCGroups.FiniteGroupClass.allFinite) hι
          (ProCGrp.allFinite_property (ProfiniteGrp.of _))
          (allFinite_freeProCZCCompletedFoxPullbackGenerator
            (X := X) (F := F) hκ η φ ι)
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
              ProCGroups.FiniteGroupClass.allFinite) X H
            (allFinite_freeProCZCCompletedFoxPullbackGenerator
              (X := X) (F := F) hκ η φ ι)) g)
        (allFinite_freeProCZCCompletedFoxJacobianMatrix
          (X := X) (F := F) hκ η φ ι) := by
  rw [allFinite_freeProCZCCompletedFoxDerivativeVector_comp
    (X := X) (Y := Y) (F := F) (F' := F') (H := H)
    hι hκ η hη_continuous φ g]
  exact allFinite_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul
    (X := X) (F := F) hκ η φ ι
    (freeProCZCCompletedFoxDerivativeVector
      (C := ProCGroups.FiniteGroupClass.allFinite) hι
      (ProCGrp.allFinite_property (ProfiniteGrp.of _))
      (allFinite_freeProCZCCompletedFoxPullbackGenerator
        (X := X) (F := F) hκ η φ ι)
      (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
          ProCGroups.FiniteGroupClass.allFinite) X H
        (allFinite_freeProCZCCompletedFoxPullbackGenerator
          (X := X) (F := F) hκ η φ ι)) g)

omit [Fintype X] in
/-- Continuous-homomorphism form of the right-homomorphism chain rule. -/
theorem allFinite_freeProCZCCompletedFoxRightHom_comp_continuousMonoidHom
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →ₜ* F') (φ : Y → H) :
    freeProCZCCompletedFoxRightHom
        (C := ProCGroups.FiniteGroupClass.allFinite) hι
        (ProCGrp.allFinite_property (ProfiniteGrp.of _))
        (allFinite_freeProCZCCompletedFoxPullbackGenerator
          (X := X) (F := F) hκ η.toMonoidHom φ ι)
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) X H
          (allFinite_freeProCZCCompletedFoxPullbackGenerator
            (X := X) (F := F) hκ η.toMonoidHom φ ι)) =
      (freeProCZCCompletedFoxRightHom
        (C := ProCGroups.FiniteGroupClass.allFinite) hκ
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Y H φ)).comp η.toMonoidHom := by
  exact allFinite_freeProCZCCompletedFoxRightHom_comp
    (X := X) (Y := Y) (F := F) (F' := F') (H := H)
    hι hκ η.toMonoidHom η.continuous_toFun φ

/-- Continuous-homomorphism form of the completed pro-\(C\) Fox chain rule in vector form. -/
theorem allFinite_freeProCZCCompletedFoxDerivativeVector_comp_continuousMonoidHom
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →ₜ* F') (φ : Y → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (C := ProCGroups.FiniteGroupClass.allFinite) hκ
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Y H φ) (η g) =
      allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (F := F) hκ η.toMonoidHom φ ι
        (freeProCZCCompletedFoxDerivativeVector
          (C := ProCGroups.FiniteGroupClass.allFinite) hι
          (ProCGrp.allFinite_property (ProfiniteGrp.of _))
          (allFinite_freeProCZCCompletedFoxPullbackGenerator
            (X := X) (F := F) hκ η.toMonoidHom φ ι)
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
              ProCGroups.FiniteGroupClass.allFinite) X H
            (allFinite_freeProCZCCompletedFoxPullbackGenerator
              (X := X) (F := F) hκ η.toMonoidHom φ ι)) g) := by
  exact allFinite_freeProCZCCompletedFoxDerivativeVector_comp
    (X := X) (Y := Y) (F := F) (F' := F') (H := H)
    hι hκ η.toMonoidHom η.continuous_toFun φ g

/-- Continuous-homomorphism form of the completed pro-\(C\) Fox chain rule in component form. -/
theorem allFinite_freeProCZCCompletedFoxDerivativeVector_comp_apply_continuousMonoidHom
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →ₜ* F') (φ : Y → H) (g : F) (y : Y) :
    freeProCZCCompletedFoxDerivativeVector
        (C := ProCGroups.FiniteGroupClass.allFinite) hκ
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Y H φ) (η g) y =
      ∑ x : X,
        freeProCZCCompletedFoxDerivativeVector
            (C := ProCGroups.FiniteGroupClass.allFinite) hι
            (ProCGrp.allFinite_property (ProfiniteGrp.of _))
            (allFinite_freeProCZCCompletedFoxPullbackGenerator
              (X := X) (F := F) hκ η.toMonoidHom φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
                ProCGroups.FiniteGroupClass.allFinite) X H
              (allFinite_freeProCZCCompletedFoxPullbackGenerator
                (X := X) (F := F) hκ η.toMonoidHom φ ι)) g x *
          allFinite_freeProCZCCompletedFoxJacobian
            (X := X) (F := F) hκ η.toMonoidHom φ ι x y := by
  exact allFinite_freeProCZCCompletedFoxDerivativeVector_comp_apply
    (X := X) (Y := Y) (F := F) (F' := F') (H := H)
    hι hκ η.toMonoidHom η.continuous_toFun φ g y

/-- The continuous-homomorphism form of the completed pro-\(C\) Fox chain rule in matrix form. -/
theorem allFinite_freeProCZCCompletedFoxDerivativeVector_comp_matrix_continuousMonoidHom
    {ι : X → F} {κ : Y → F'}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (η : F →ₜ* F') (φ : Y → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (C := ProCGroups.FiniteGroupClass.allFinite) hκ
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Y H φ) (η g) =
      Matrix.vecMul
        (freeProCZCCompletedFoxDerivativeVector
          (C := ProCGroups.FiniteGroupClass.allFinite) hι
          (ProCGrp.allFinite_property (ProfiniteGrp.of _))
          (allFinite_freeProCZCCompletedFoxPullbackGenerator
            (X := X) (F := F) hκ η.toMonoidHom φ ι)
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
              ProCGroups.FiniteGroupClass.allFinite) X H
            (allFinite_freeProCZCCompletedFoxPullbackGenerator
              (X := X) (F := F) hκ η.toMonoidHom φ ι)) g)
        (allFinite_freeProCZCCompletedFoxJacobianMatrix
          (X := X) (F := F) hκ η.toMonoidHom φ ι) := by
  exact allFinite_freeProCZCCompletedFoxDerivativeVector_comp_matrix
    (X := X) (Y := Y) (F := F) (F' := F') (H := H)
    hι hκ η.toMonoidHom η.continuous_toFun φ g

end AllFiniteChainRule

end

end FoxDifferential
