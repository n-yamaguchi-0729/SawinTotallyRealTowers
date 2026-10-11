/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.ChainRule.Basic

/-!
# Fox differential: completed — continuous — chain rule — iterated

The principal declarations in this module are:

- `allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator`
  The pulled-back target generator on the middle free source in a two-step source chain.
- `allFinite_freeProCZCCompletedFoxFirstPullbackGenerator`
  The pulled-back target generator on the first free source in a two-step source chain.
- `allFinite_freeProCZCCompletedFoxJacobianLinearMap_comp_comp`
  Completed Fox-Jacobian functoriality for two composable continuous free pro-\(C\) source maps, as
  a composition of finite linear maps.
- `allFinite_freeProCZCCompletedFoxJacobianMatrix_comp_comp`
  Completed Fox-Jacobian functoriality for two composable continuous free pro-\(C\) source maps, as
  a matrix product.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u

section AllFiniteIteratedChainRule

variable {X Y Z F F' F'' H : Type u}
variable [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
variable [Fintype Y] [DecidableEq Y] [TopologicalSpace Y] [DiscreteTopology Y]
variable [DecidableEq Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
variable [Group F''] [TopologicalSpace F''] [IsTopologicalGroup F'']
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable [CompactSpace F'] [T2Space F'] [TotallyDisconnectedSpace F']
variable [CompactSpace F''] [T2Space F''] [TotallyDisconnectedSpace F'']
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- The pulled-back target generator on the middle free source in a two-step source chain. -/
abbrev allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
    {mu : Z → F''}
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) mu)
    (θ : F' →* F'') (φ : Z → H) (κ : Y → F') : Y → H :=
  allFinite_freeProCZCCompletedFoxPullbackGenerator
    (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ

/-- The pulled-back target generator on the first free source in a two-step source chain. -/
abbrev allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
    {κ : Y → F'} {mu : Z → F''}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) mu)
    (η : F →* F') (θ : F' →* F'') (φ : Z → H) (ι : X → F) : X → H :=
  allFinite_freeProCZCCompletedFoxPullbackGenerator
    (X := X) (Y := Y) (F := F) (F' := F') hκ η
    (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
      (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
    ι

omit [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [IsTopologicalGroup F] in
/--
Completed Fox-Jacobian functoriality for two composable continuous free pro-\(C\) source maps,
as a composition of finite linear maps.
-/
theorem allFinite_freeProCZCCompletedFoxJacobianLinearMap_comp_comp
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) mu)
    (η : F →* F') (θ : F' →* F'') (hθ_continuous : Continuous θ) (φ : Z → H) :
    allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (Y := Z) (F := F) (F' := F'') hmu (θ.comp η) φ ι =
      (allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ).comp
        (allFinite_freeProCZCCompletedFoxJacobianLinearMap
          (X := X) (Y := Y) (F := F) (F' := F') hκ η
          (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
          ι) := by
  classical
  apply linearMap_ext_pi_single
  intro x
  have hchain := allFinite_freeProCZCCompletedFoxDerivativeVector_comp
    (X := Y) (Y := Z) (F := F') (F' := F'') (H := H)
    hκ hmu θ hθ_continuous φ (η (ι x))
  simpa [LinearMap.comp_apply,
    allFinite_freeProCZCCompletedFoxJacobianLinearMap,
    allFinite_freeProCZCCompletedFoxJacobian,
    allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator] using hchain

omit [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [IsTopologicalGroup F] in
/--
Completed Fox-Jacobian functoriality for two composable continuous free pro-\(C\) source maps,
as a matrix product.
-/
theorem allFinite_freeProCZCCompletedFoxJacobianMatrix_comp_comp
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) mu)
    (η : F →* F') (θ : F' →* F'') (hθ_continuous : Continuous θ) (φ : Z → H) :
    allFinite_freeProCZCCompletedFoxJacobianMatrix
        (X := X) (Y := Z) (F := F) (F' := F'') hmu (θ.comp η) φ ι =
      allFinite_freeProCZCCompletedFoxJacobianMatrix
          (X := X) (Y := Y) (F := F) (F' := F') hκ η
          (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
          ι *
        allFinite_freeProCZCCompletedFoxJacobianMatrix
          (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ := by
  apply Matrix.ext
  intro x z
  have h := congrFun
    (allFinite_freeProCZCCompletedFoxDerivativeVector_comp
      (X := Y) (Y := Z) (F := F') (F' := F'') (H := H)
      hκ hmu θ hθ_continuous φ (η (ι x))) z
  simpa [Matrix.mul_apply,
    allFinite_freeProCZCCompletedFoxJacobianMatrix,
    allFinite_freeProCZCCompletedFoxJacobian,
    allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator] using h

/-- Three-term completed pro-\(C\) Fox chain rule in vector form. -/
theorem allFinite_freeProCZCCompletedFoxDerivativeVector_comp_comp
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) mu)
    (η : F →* F') (hη_continuous : Continuous η)
    (θ : F' →* F'') (hθ_continuous : Continuous θ) (φ : Z → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (C := ProCGroups.FiniteGroupClass.allFinite) hmu
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Z H φ) (θ (η g)) =
      allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ
        (allFinite_freeProCZCCompletedFoxJacobianLinearMap
          (X := X) (Y := Y) (F := F) (F' := F') hκ η
          (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
          ι
          (freeProCZCCompletedFoxDerivativeVector
            (C := ProCGroups.FiniteGroupClass.allFinite) hι
            (ProCGrp.allFinite_property (ProfiniteGrp.of _))
            (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
              (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
              hκ hmu η θ φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
                ProCGroups.FiniteGroupClass.allFinite) X H
              (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η θ φ ι)) g)) := by
  calc
    freeProCZCCompletedFoxDerivativeVector
        (C := ProCGroups.FiniteGroupClass.allFinite) hmu
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Z H φ) (θ (η g)) =
      allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ
        (freeProCZCCompletedFoxDerivativeVector
          (C := ProCGroups.FiniteGroupClass.allFinite) hκ
          (ProCGrp.allFinite_property (ProfiniteGrp.of _))
          (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
              ProCGroups.FiniteGroupClass.allFinite) Y H
            (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
              (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)) (η g)) := by
        exact allFinite_freeProCZCCompletedFoxDerivativeVector_comp
          (X := Y) (Y := Z) (F := F') (F' := F'') (H := H)
          hκ hmu θ hθ_continuous φ (η g)
    _ =
      allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ
        (allFinite_freeProCZCCompletedFoxJacobianLinearMap
          (X := X) (Y := Y) (F := F) (F' := F') hκ η
          (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
          ι
          (freeProCZCCompletedFoxDerivativeVector
            (C := ProCGroups.FiniteGroupClass.allFinite) hι
            (ProCGrp.allFinite_property (ProfiniteGrp.of _))
            (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
              (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
              hκ hmu η θ φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
                ProCGroups.FiniteGroupClass.allFinite) X H
              (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η θ φ ι)) g)) := by
        exact congrArg
          (allFinite_freeProCZCCompletedFoxJacobianLinearMap
            (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ)
          (allFinite_freeProCZCCompletedFoxDerivativeVector_comp
            (X := X) (Y := Y) (F := F) (F' := F') (H := H)
            hι hκ η hη_continuous
            (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
              (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ) g)

/-- The three-term completed pro-\(C\) Fox chain rule in matrix form. -/
theorem allFinite_freeProCZCCompletedFoxDerivativeVector_comp_comp_matrix
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) mu)
    (η : F →* F') (hη_continuous : Continuous η)
    (θ : F' →* F'') (hθ_continuous : Continuous θ) (φ : Z → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (C := ProCGroups.FiniteGroupClass.allFinite) hmu
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Z H φ) (θ (η g)) =
      Matrix.vecMul
        (Matrix.vecMul
          (freeProCZCCompletedFoxDerivativeVector
            (C := ProCGroups.FiniteGroupClass.allFinite) hι
            (ProCGrp.allFinite_property (ProfiniteGrp.of _))
            (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
              (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
              hκ hmu η θ φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
                ProCGroups.FiniteGroupClass.allFinite) X H
              (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η θ φ ι)) g)
          (allFinite_freeProCZCCompletedFoxJacobianMatrix
            (X := X) (Y := Y) (F := F) (F' := F') hκ η
            (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
              (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
            ι))
        (allFinite_freeProCZCCompletedFoxJacobianMatrix
          (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ) := by
  rw [allFinite_freeProCZCCompletedFoxDerivativeVector_comp_comp
    (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
    hι hκ hmu η hη_continuous θ hθ_continuous φ g]
  rw [allFinite_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul]
  rw [allFinite_freeProCZCCompletedFoxJacobianLinearMap_eq_vecMul]

/-- Three-term completed pro-\(C\) Fox chain rule in component form. -/
theorem allFinite_freeProCZCCompletedFoxDerivativeVector_comp_comp_apply
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) mu)
    (η : F →* F') (hη_continuous : Continuous η)
    (θ : F' →* F'') (hθ_continuous : Continuous θ) (φ : Z → H) (g : F) (z : Z) :
    freeProCZCCompletedFoxDerivativeVector
        (C := ProCGroups.FiniteGroupClass.allFinite) hmu
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Z H φ) (θ (η g)) z =
      ∑ y : Y,
        (∑ x : X,
          freeProCZCCompletedFoxDerivativeVector
              (C := ProCGroups.FiniteGroupClass.allFinite) hι
              (ProCGrp.allFinite_property (ProfiniteGrp.of _))
              (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η θ φ ι)
              (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
                  ProCGroups.FiniteGroupClass.allFinite) X H
                (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
                  (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                  hκ hmu η θ φ ι)) g x *
            allFinite_freeProCZCCompletedFoxJacobian
              (X := X) (Y := Y) (F := F) (F' := F') hκ η
              (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
                (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ φ κ)
              ι x y) *
          allFinite_freeProCZCCompletedFoxJacobian
            (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ φ κ y z := by
  have h := congrFun
      (allFinite_freeProCZCCompletedFoxDerivativeVector_comp_comp_matrix
        (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
      hι hκ hmu η hη_continuous θ hθ_continuous φ g) z
  simpa [Matrix.vecMul, dotProduct,
    allFinite_freeProCZCCompletedFoxJacobianMatrix] using h

omit [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [IsTopologicalGroup F] [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F] in
/--
Continuous-homomorphism form of completed Fox-Jacobian functoriality, as a composition of finite
linear maps.
-/
theorem allFinite_freeProCZCCompletedFoxJacobianLinearMap_comp_comp_continuousMonoidHom
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) mu)
    (η : F →ₜ* F') (θ : F' →ₜ* F'') (φ : Z → H) :
    allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := X) (Y := Z) (F := F) (F' := F'') hmu
        (θ.toMonoidHom.comp η.toMonoidHom) φ ι =
      (allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ.toMonoidHom φ κ).comp
        (allFinite_freeProCZCCompletedFoxJacobianLinearMap
          (X := X) (Y := Y) (F := F) (F' := F') hκ η.toMonoidHom
          (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ.toMonoidHom φ κ)
          ι) := by
  exact allFinite_freeProCZCCompletedFoxJacobianLinearMap_comp_comp
    (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
    hκ hmu η.toMonoidHom θ.toMonoidHom θ.continuous_toFun φ

omit [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
    [IsTopologicalGroup F] [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F] in
/-- Continuous-homomorphism form of completed Fox-Jacobian functoriality, as a matrix product. -/
theorem allFinite_freeProCZCCompletedFoxJacobianMatrix_comp_comp_continuousMonoidHom
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) mu)
    (η : F →ₜ* F') (θ : F' →ₜ* F'') (φ : Z → H) :
    allFinite_freeProCZCCompletedFoxJacobianMatrix
        (X := X) (Y := Z) (F := F) (F' := F'') hmu
        (θ.toMonoidHom.comp η.toMonoidHom) φ ι =
      allFinite_freeProCZCCompletedFoxJacobianMatrix
          (X := X) (Y := Y) (F := F) (F' := F') hκ η.toMonoidHom
          (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ.toMonoidHom φ κ)
          ι *
        allFinite_freeProCZCCompletedFoxJacobianMatrix
          (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ.toMonoidHom φ κ := by
  exact allFinite_freeProCZCCompletedFoxJacobianMatrix_comp_comp
    (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
    hκ hmu η.toMonoidHom θ.toMonoidHom θ.continuous_toFun φ

/-- Continuous-homomorphism form of the three-term completed pro-\(C\) Fox chain rule. -/
theorem allFinite_freeProCZCCompletedFoxDerivativeVector_comp_comp_continuousMonoidHom
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) mu)
    (η : F →ₜ* F') (θ : F' →ₜ* F'') (φ : Z → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (C := ProCGroups.FiniteGroupClass.allFinite) hmu
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Z H φ) (θ (η g)) =
      allFinite_freeProCZCCompletedFoxJacobianLinearMap
        (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ.toMonoidHom φ κ
        (allFinite_freeProCZCCompletedFoxJacobianLinearMap
          (X := X) (Y := Y) (F := F) (F' := F') hκ η.toMonoidHom
          (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
            (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ.toMonoidHom φ κ)
          ι
          (freeProCZCCompletedFoxDerivativeVector
            (C := ProCGroups.FiniteGroupClass.allFinite) hι
            (ProCGrp.allFinite_property (ProfiniteGrp.of _))
            (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
              (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
              hκ hmu η.toMonoidHom θ.toMonoidHom φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
                ProCGroups.FiniteGroupClass.allFinite) X H
              (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η.toMonoidHom θ.toMonoidHom φ ι)) g)) := by
  exact allFinite_freeProCZCCompletedFoxDerivativeVector_comp_comp
    (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
    hι hκ hmu η.toMonoidHom η.continuous_toFun θ.toMonoidHom θ.continuous_toFun φ g

/--
The continuous-homomorphism form of the three-term completed pro-\(C\) Fox chain rule in matrix
form.
-/
theorem allFinite_freeProCZCCompletedFoxDerivativeVector_comp_comp_matrix_continuousMonoidHom
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) mu)
    (η : F →ₜ* F') (θ : F' →ₜ* F'') (φ : Z → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (C := ProCGroups.FiniteGroupClass.allFinite) hmu
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Z H φ) (θ (η g)) =
      Matrix.vecMul
        (Matrix.vecMul
          (freeProCZCCompletedFoxDerivativeVector
            (C := ProCGroups.FiniteGroupClass.allFinite) hι
            (ProCGrp.allFinite_property (ProfiniteGrp.of _))
            (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
              (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
              hκ hmu η.toMonoidHom θ.toMonoidHom φ ι)
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
                ProCGroups.FiniteGroupClass.allFinite) X H
              (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η.toMonoidHom θ.toMonoidHom φ ι)) g)
          (allFinite_freeProCZCCompletedFoxJacobianMatrix
            (X := X) (Y := Y) (F := F) (F' := F') hκ η.toMonoidHom
            (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
              (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ.toMonoidHom φ κ)
            ι))
        (allFinite_freeProCZCCompletedFoxJacobianMatrix
          (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ.toMonoidHom φ κ) := by
  exact allFinite_freeProCZCCompletedFoxDerivativeVector_comp_comp_matrix
    (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
    hι hκ hmu η.toMonoidHom η.continuous_toFun θ.toMonoidHom θ.continuous_toFun φ g

/--
Continuous-homomorphism form of the three-term completed pro-\(C\) Fox chain rule in component
form.
-/
theorem allFinite_freeProCZCCompletedFoxDerivativeVector_comp_comp_apply_continuousMonoidHom
    {ι : X → F} {κ : Y → F'} {mu : Z → F''}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) ι)
    (hκ : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) κ)
    (hmu : ProCGroups.FreeProC.IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite) mu)
    (η : F →ₜ* F') (θ : F' →ₜ* F'') (φ : Z → H) (g : F) (z : Z) :
    freeProCZCCompletedFoxDerivativeVector
        (C := ProCGroups.FiniteGroupClass.allFinite) hmu
        (ProCGrp.allFinite_property (ProfiniteGrp.of _)) φ
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
            ProCGroups.FiniteGroupClass.allFinite) Z H φ) (θ (η g)) z =
      ∑ y : Y,
        (∑ x : X,
          freeProCZCCompletedFoxDerivativeVector
              (C := ProCGroups.FiniteGroupClass.allFinite) hι
              (ProCGrp.allFinite_property (ProfiniteGrp.of _))
              (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
                (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                hκ hmu η.toMonoidHom θ.toMonoidHom φ ι)
              (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C :=
                  ProCGroups.FiniteGroupClass.allFinite) X H
                (allFinite_freeProCZCCompletedFoxFirstPullbackGenerator
                  (X := X) (F := F) (Y := Y) (F' := F') (Z := Z) (F'' := F'')
                  hκ hmu η.toMonoidHom θ.toMonoidHom φ ι)) g x *
            allFinite_freeProCZCCompletedFoxJacobian
              (X := X) (Y := Y) (F := F) (F' := F') hκ η.toMonoidHom
              (allFinite_freeProCZCCompletedFoxMiddlePullbackGenerator
                (Y := Y) (F' := F') (Z := Z) (F'' := F'') hmu θ.toMonoidHom φ κ)
              ι x y) *
          allFinite_freeProCZCCompletedFoxJacobian
            (X := Y) (Y := Z) (F := F') (F' := F'') hmu θ.toMonoidHom φ κ y z := by
  exact allFinite_freeProCZCCompletedFoxDerivativeVector_comp_comp_apply
    (X := X) (Y := Y) (Z := Z) (F := F) (F' := F') (F'' := F'') (H := H)
    hι hκ hmu η.toMonoidHom η.continuous_toFun θ.toMonoidHom θ.continuous_toFun φ g z

end AllFiniteIteratedChainRule

end

end FoxDifferential
