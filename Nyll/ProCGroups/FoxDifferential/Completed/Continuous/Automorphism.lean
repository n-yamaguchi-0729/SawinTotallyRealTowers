/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.ChainRule.Iterated
import Nyll.ProCGroups.FoxDifferential.Common.Jacobian

/-!
# Fox differential: completed — continuous — automorphism

The principal declarations in this module are:

- `allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse`
  The named inverse linear map for the completed Fox-Jacobian of a continuous automorphism.
- `allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse`
  The named inverse matrix for the completed Fox-Jacobian of a continuous automorphism.
- `allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage_apply`
  Evaluation of the finite-stage inverse matrix for a completed Fox-Jacobian of a continuous
  automorphism.
- `allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse_eq_vecMul`
  The named inverse linear map is row-vector multiplication by the named inverse matrix.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v

section AllFiniteAutomorphismJacobian

variable {X F H : Type u}
variable [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- The named inverse linear map for the completed Fox-Jacobian of a continuous automorphism. -/
def allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (e : F ≃* F) (φ : X → H) :
    ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := X) (H := H)
        →ₗ[ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H]
      ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := X) (H := H) :=
  allFinite_freeProCZCCompletedFoxJacobianLinearMap
    (X := X) (Y := X) (F := F) (F' := F) hι e.symm.toMonoidHom
    (allFinite_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hι e.toMonoidHom φ ι)
    ι

/-- The named inverse matrix for the completed Fox-Jacobian of a continuous automorphism. -/
def allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (e : F ≃* F) (φ : X → H) :
    Matrix X X (ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H) :=
  allFinite_freeProCZCCompletedFoxJacobianMatrix
    (X := X) (Y := X) (F := F) (F' := F) hι e.symm.toMonoidHom
    (allFinite_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hι e.toMonoidHom φ ι)
    ι

/--
A finite-stage projection of the named inverse matrix for a completed Fox-Jacobian of a
continuous automorphism.
-/
def allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (e : F ≃* F) (φ : X → H)
    (j : ZCCompletedGroupAlgebraIndex ProCGroups.FiniteGroupClass.allFinite H) :
    Matrix X X (ZCCompletedGroupAlgebraStage ProCGroups.FiniteGroupClass.allFinite H j) :=
  fun x y =>
    zcCompletedGroupAlgebraProjection ProCGroups.FiniteGroupClass.allFinite H j
      (allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse
        (X := X) (F := F) (H := H) hι e φ x y)

omit [Fintype X] in
/--
Evaluation of the finite-stage inverse matrix for a completed Fox-Jacobian of a continuous
automorphism.
-/
@[simp]
theorem allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage_apply
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (e : F ≃* F) (φ : X → H)
    (j : ZCCompletedGroupAlgebraIndex ProCGroups.FiniteGroupClass.allFinite H) (x y : X) :
    allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage
        (X := X) (F := F) (H := H) hι e φ j x y =
      zcCompletedGroupAlgebraProjection ProCGroups.FiniteGroupClass.allFinite H j
        (allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse
          (X := X) (F := F) (H := H) hι e φ x y) :=
  rfl

/-- The named inverse linear map is row-vector multiplication by the named inverse matrix. -/
theorem allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse_eq_vecMul
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (e : F ≃* F) (φ : X → H)
    (v : ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := X) (H := H)) :
    allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse
        (X := X) (F := F) (H := H) hι e φ v =
      Matrix.vecMul v
        (allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse
          (X := X) (F := F) (H := H) hι e φ) := by
  exact allFinite_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul
    (X := X) (F := F) hι e.symm.toMonoidHom
    (allFinite_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hι e.toMonoidHom φ ι)
    ι v

omit [Fintype X] in
/--
Pulling the target generator map first along an automorphism and then along its inverse recovers
the original generator map.
-/
theorem allFinite_freeProCZCCompletedFoxAutomorphism_pullback_symm
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (φ : X → H) :
    allFinite_freeProCZCCompletedFoxPullbackGenerator
        (X := X) (F := F) hι e.symm.toMonoidHom
        (allFinite_freeProCZCCompletedFoxPullbackGenerator
          (X := X) (F := F) hι e.toMonoidHom φ ι)
        ι =
      φ := by
  let htarget :
      ProCGroups.ProC.HasOpenNormalBasisInClass ProCGroups.FiniteGroupClass.allFinite
        (ZCCompletedFoxSemidirect ProCGroups.FiniteGroupClass.allFinite X H) :=
    ProCGrp.allFinite_property (ProfiniteGrp.of _)
  let hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C :=
      ProCGroups.FiniteGroupClass.allFinite) φ) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
        ProCGroups.FiniteGroupClass.allFinite) X H φ
  let φe : X → H :=
    allFinite_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hι e.toMonoidHom φ ι
  let hφe : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C :=
      ProCGroups.FiniteGroupClass.allFinite) φe) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
        ProCGroups.FiniteGroupClass.allFinite) X H φe
  have hρ := allFinite_freeProCZCCompletedFoxRightHom_comp
    (X := X) (Y := X) (F := F) (F' := F) (H := H)
    hι hι e.toMonoidHom he_continuous φ
  funext x
  change freeProCZCCompletedFoxRightHom
      (C := ProCGroups.FiniteGroupClass.allFinite) hι htarget φe hφe
      (e.symm (ι x)) = φ x
  have happ := congrFun (congrArg DFunLike.coe hρ) (e.symm (ι x))
  change
    freeProCZCCompletedFoxRightHom
        (C := ProCGroups.FiniteGroupClass.allFinite) hι htarget φe hφe
        (e.symm (ι x)) =
      ((freeProCZCCompletedFoxRightHom
        (C := ProCGroups.FiniteGroupClass.allFinite) hι htarget φ hφ).comp
        e.toMonoidHom) (e.symm (ι x)) at happ
  calc
    freeProCZCCompletedFoxRightHom
        (C := ProCGroups.FiniteGroupClass.allFinite) hι htarget φe hφe
        (e.symm (ι x)) =
        ((freeProCZCCompletedFoxRightHom
          (C := ProCGroups.FiniteGroupClass.allFinite) hι htarget φ hφ).comp
          e.toMonoidHom) (e.symm (ι x)) := by
          exact happ
    _ = freeProCZCCompletedFoxRightHom
        (C := ProCGroups.FiniteGroupClass.allFinite) hι htarget φ hφ (ι x) := by
          simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_ofClass,
              Function.comp_apply,
  MulEquiv.apply_symm_apply, freeProCZCCompletedFoxRightHom_apply,
      freeProCZCCompletedFoxSemidirectLift_generator,
  freeProCZCCompletedFoxSemidirectGenerator_right]
    _ = φ x := by
          simp only [freeProCZCCompletedFoxRightHom_apply,
              freeProCZCCompletedFoxSemidirectLift_generator,
  freeProCZCCompletedFoxSemidirectGenerator_right]

/--
Composing the completed Fox-Jacobian linear map of a continuous automorphism with its named
inverse gives the identity.
-/
theorem allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMap_comp_inverse
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (φ : X → H) :
    (allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι).comp
      (allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse
        (X := X) (F := F) (H := H) hι e φ) =
      LinearMap.id := by
  apply linearMap_ext_pi_single
  intro x
  have hchain := allFinite_freeProCZCCompletedFoxDerivativeVector_comp
    (X := X) (Y := X) (F := F) (F' := F) (H := H)
    hι hι e.toMonoidHom he_continuous φ (e.symm (ι x))
  convert hchain.symm using 1
  all_goals
    simp only [LinearMap.comp_apply,
      allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse,
      allFinite_freeProCZCCompletedFoxJacobianLinearMap,
      foxJacobianLinearMap_single, allFinite_freeProCZCCompletedFoxJacobian,
      LinearMap.id_coe, id_eq, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulEquiv.apply_symm_apply]
  all_goals try rfl
  exact (freeProCZCCompletedFoxDerivativeVector_generator
    (C := ProCGroups.FiniteGroupClass.allFinite) hι
    (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
    (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
      (C := ProCGroups.FiniteGroupClass.allFinite) X H φ) x).symm

/--
Composing the named inverse for the completed Fox-Jacobian linear map of a continuous
automorphism with the Jacobian gives the identity.
-/
theorem allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMap_inverse_comp
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (he_symm_continuous : Continuous e.symm)
    (φ : X → H) :
    (allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse
        (X := X) (F := F) (H := H) hι e φ).comp
      (allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι) =
      LinearMap.id := by
  apply linearMap_ext_pi_single
  intro x
  let φe : X → H :=
    allFinite_freeProCZCCompletedFoxPullbackGenerator
      (X := X) (F := F) hι e.toMonoidHom φ ι
  have hpull :
      allFinite_freeProCZCCompletedFoxPullbackGenerator
          (X := X) (F := F) hι e.symm.toMonoidHom φe ι =
        φ := by
    simpa [φe] using
      allFinite_freeProCZCCompletedFoxAutomorphism_pullback_symm
        (X := X) (F := F) (H := H) hι e he_continuous φ
  have hchain := allFinite_freeProCZCCompletedFoxDerivativeVector_comp
    (X := X) (Y := X) (F := F) (F' := F) (H := H)
    hι hι e.symm.toMonoidHom he_symm_continuous φe (e (ι x))
  rw [hpull] at hchain
  convert hchain.symm using 1
  · simp only [
      allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse,
      allFinite_freeProCZCCompletedFoxJacobianLinearMap,
      MulEquiv.toMonoidHom_eq_coe, LinearMap.comp_apply,
      foxJacobianLinearMap_single, allFinite_freeProCZCCompletedFoxJacobian,
      MonoidHom.coe_ofClass, φe]
  · simpa only [LinearMap.id_coe, id_eq, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, MulEquiv.symm_apply_apply] using
      (freeProCZCCompletedFoxDerivativeVector_generator
      (C := ProCGroups.FiniteGroupClass.allFinite) hι
      (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φe
      (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
        (C := ProCGroups.FiniteGroupClass.allFinite) X H φe) x).symm

/--
The named inverse matrix is a left inverse for the completed Fox-Jacobian matrix of a continuous
automorphism.
-/
theorem allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse_mul
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (φ : X → H) :
    allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse
        (X := X) (F := F) (H := H) hι e φ *
      allFinite_freeProCZCCompletedFoxJacobianMatrix
        (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι =
      (1 : Matrix X X (ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H)) := by
  rw [Matrix.ext_iff_vecMul]
  intro v
  have hlin :=
    allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMap_comp_inverse
      (X := X) (F := F) (H := H) hι e he_continuous φ
  have happ := congrFun (congrArg DFunLike.coe hlin) v
  simpa [LinearMap.comp_apply,
    allFinite_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul,
    allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse_eq_vecMul,
    Matrix.vecMul_vecMul, Matrix.vecMul_one] using happ

/--
The named inverse matrix is a right inverse for the completed Fox-Jacobian matrix of a
continuous automorphism.
-/
theorem allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrix_mul_inverse
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (he_symm_continuous : Continuous e.symm)
    (φ : X → H) :
    allFinite_freeProCZCCompletedFoxJacobianMatrix
        (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι *
      allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse
        (X := X) (F := F) (H := H) hι e φ =
      (1 : Matrix X X (ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H)) := by
  rw [Matrix.ext_iff_vecMul]
  intro v
  have hlin :=
    allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMap_inverse_comp
      (X := X) (F := F) (H := H) hι e he_continuous he_symm_continuous φ
  have happ := congrFun (congrArg DFunLike.coe hlin) v
  simpa [LinearMap.comp_apply,
    allFinite_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul,
    allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse_eq_vecMul,
    Matrix.vecMul_vecMul, Matrix.vecMul_one] using happ

/--
The finite-stage inverse matrix is a left inverse for the finite-stage completed Fox-Jacobian
matrix of a continuous automorphism.
-/
theorem allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixStageInverse_mul
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (φ : X → H)
    (j : ZCCompletedGroupAlgebraIndex ProCGroups.FiniteGroupClass.allFinite H) :
    allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage
        (X := X) (F := F) (H := H) hι e φ j *
      allFinite_freeProCZCCompletedFoxJacobianMatrixStage
        (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι j =
      (1 : Matrix X X (ZCCompletedGroupAlgebraStage ProCGroups.FiniteGroupClass.allFinite H j))
          := by
  apply Matrix.ext
  intro x y
  have h := congrArg
    (fun M : Matrix X X (ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H) =>
      zcCompletedGroupAlgebraProjection ProCGroups.FiniteGroupClass.allFinite H j (M x y))
    (allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverse_mul
      (X := X) (F := F) (H := H) hι e he_continuous φ)
  have hone :
      zcCompletedGroupAlgebraProjection ProCGroups.FiniteGroupClass.allFinite H j
          ((1 : Matrix X X (ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H)) x y) =
        (1 : Matrix X X (ZCCompletedGroupAlgebraStage ProCGroups.FiniteGroupClass.allFinite H
            j)) x y := by
    by_cases hxy : x = y
    · subst y
      simp only [zcCompletedGroupAlgebraProjection, Matrix.one_apply_eq,
          zcCompletedGroupAlgebraProjection_one]
    · simp only [zcCompletedGroupAlgebraProjection, ne_eq, hxy, not_false_eq_true,
        Matrix.one_apply_ne,
  zcCompletedGroupAlgebraProjection_zero]
  simp only [Matrix.mul_apply] at h
  rw [zcCompletedGroupAlgebraProjection_sum] at h
  rw [hone] at h
  simp only [zcCompletedGroupAlgebraProjection, MulEquiv.toMonoidHom_eq_coe,
  allFinite_freeProCZCCompletedFoxJacobianMatrix_apply, zcCompletedGroupAlgebraProjection_mul] at h
  simpa [Matrix.mul_apply,
    allFinite_freeProCZCCompletedFoxJacobianMatrixStage,
    allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage] using h

/--
The finite-stage inverse matrix is a right inverse for the finite-stage completed Fox-Jacobian
matrix of a continuous automorphism.
-/
theorem allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixStage_mul_inverse
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (he_symm_continuous : Continuous e.symm)
    (φ : X → H) (j : ZCCompletedGroupAlgebraIndex ProCGroups.FiniteGroupClass.allFinite H) :
    allFinite_freeProCZCCompletedFoxJacobianMatrixStage
        (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι j *
      allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage
        (X := X) (F := F) (H := H) hι e φ j =
      (1 : Matrix X X (ZCCompletedGroupAlgebraStage ProCGroups.FiniteGroupClass.allFinite H j))
          := by
  apply Matrix.ext
  intro x y
  have h := congrArg
    (fun M : Matrix X X (ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H) =>
      zcCompletedGroupAlgebraProjection ProCGroups.FiniteGroupClass.allFinite H j (M x y))
    (allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrix_mul_inverse
      (X := X) (F := F) (H := H) hι e he_continuous he_symm_continuous φ)
  have hone :
      zcCompletedGroupAlgebraProjection ProCGroups.FiniteGroupClass.allFinite H j
          ((1 : Matrix X X (ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H)) x y) =
        (1 : Matrix X X (ZCCompletedGroupAlgebraStage ProCGroups.FiniteGroupClass.allFinite H
            j)) x y := by
    by_cases hxy : x = y
    · subst y
      simp only [zcCompletedGroupAlgebraProjection, Matrix.one_apply_eq,
          zcCompletedGroupAlgebraProjection_one]
    · simp only [zcCompletedGroupAlgebraProjection, ne_eq, hxy, not_false_eq_true,
        Matrix.one_apply_ne,
  zcCompletedGroupAlgebraProjection_zero]
  simp only [Matrix.mul_apply] at h
  rw [zcCompletedGroupAlgebraProjection_sum] at h
  rw [hone] at h
  simp only [zcCompletedGroupAlgebraProjection, MulEquiv.toMonoidHom_eq_coe,
  allFinite_freeProCZCCompletedFoxJacobianMatrix_apply, zcCompletedGroupAlgebraProjection_mul] at h
  simpa [Matrix.mul_apply,
    allFinite_freeProCZCCompletedFoxJacobianMatrixStage,
    allFinite_freeProCZCCompletedFoxAutomorphismJacobianMatrixInverseStage] using h

/-- The completed Fox-Jacobian of a continuous automorphism is bundled into a linear equivalence. -/
def allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearEquiv
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (e : F ≃* F) (he_continuous : Continuous e) (he_symm_continuous : Continuous e.symm)
    (φ : X → H) :
    ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := X) (H := H)
        ≃ₗ[ZCCompletedGroupAlgebra ProCGroups.FiniteGroupClass.allFinite H]
      ZCFreeFoxCoordinates ProCGroups.FiniteGroupClass.allFinite (X := X) (H := H) := by
  refine LinearEquiv.ofLinearMap
    (allFinite_freeProCZCCompletedFoxJacobianLinearMap
      (X := X) (Y := X) (F := F) (F' := F) hι e.toMonoidHom φ ι)
    (allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMapInverse
      (X := X) (F := F) (H := H) hι e φ)
    ?_ ?_
  · exact allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMap_comp_inverse
      (X := X) (F := F) (H := H) hι e he_continuous φ
  · exact allFinite_freeProCZCCompletedFoxAutomorphismJacobianLinearMap_inverse_comp
      (X := X) (F := F) (H := H) hι e he_continuous he_symm_continuous φ

end AllFiniteAutomorphismJacobian

end

end FoxDifferential
