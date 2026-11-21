/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.InfinitePlaceModel
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedAction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completion

/-!
# Archimedean relative-idele factors as induced local blocks

The concrete archimedean completion `w.Completion` used by the adele
library is canonically the completion of the underlying absolute value
`w.1`.  Base change along this equivalence connects the actual
archimedean component of a relative idele to the local tensor block of
the local tensor decomposition, equivariantly for the full Galois action.
-/



@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open HilbertRamification

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- Completion comparison commutes with conjugation on the second
tensor factor. -/
theorem infinitePlaceLocalTensorAlgEquiv_conjugation
    (w : InfinitePlace K)
    (σ : L ≃ₐ[K] L)
    (z : w.Completion ⊗[K] L) :
    infinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) w
        (scalarTensorConjugation
          (K := K) (L := L)
          (A := w.Completion) σ z) =
      localTensorConjugation
        (K := K) (L := L) w.1 σ
        (infinitePlaceLocalTensorAlgEquiv
          (K := K) (L := L) w z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- The completion comparison on units is equivariant. -/
theorem infinitePlaceLocalTensorUnitsEquiv_smul
    (w : InfinitePlace K)
    (σ : L ≃ₐ[K] L)
    (z : (w.Completion ⊗[K] L)ˣ) :
    let := scalarTensorUnitsAction
      (K := K) (L := L) (A := w.Completion)
    let := localTensorUnitsAction
      (K := K) (L := L) w.1
    infinitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) w (σ • z) =
      σ • infinitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) w z := by
  intro sharedOwner1 sharedOwner2
  apply Units.ext
  exact infinitePlaceLocalTensorAlgEquiv_conjugation
    (K := K) (L := L) w σ
      (z : w.Completion ⊗[K] L)

section Galois

variable [IsGalois K L]

/-- The local tensor decomposition for the actual archimedean component type used by the
relative idele restricted product. -/
noncomputable def
    infinitePlaceTensorUnitsEquivLocalPlaceBlock
    (w : InfinitePlace K)
    (hw : w.1.IsNontrivial)
    (u : AbsoluteValueExtension w.1 L) :
    let :=
      decompositionGroupLocalUnitsAction w.1 hw u
    let hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) u.1
    let : SMul K u.1.Completion := hK.toSMul
    let :=
      AbsoluteValue.completionAlgebra
        w.1 u.1 u.2
    let : ∀ u' : AbsoluteValueExtension w.1 L,
        Algebra w.1.Completion u'.1.Completion :=
      fun u' =>
        AbsoluteValue.completionAlgebra
          w.1 u'.1 u'.2
    (w.Completion ⊗[K] L)ˣ ≃*
      LocalPlaceBlock w.1 hw u := by
  intro sharedOwner1 hK sharedOwner3 sharedOwner4 sharedOwner5
  exact
    (infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) w).trans
      (localTensorUnitsEquivLocalPlaceBlock
        w.1 hw u)

section Equivariance

variable
    (w : InfinitePlace K)
    (hw : w.1.IsNontrivial)
    (u : AbsoluteValueExtension w.1 L)

local instance infinitePlaceExtensionCompletionAlgebra :
    Algebra K u.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := K) u.1

local instance infinitePlaceExtensionCompletionSMul :
    SMul K u.1.Completion :=
  infinitePlaceExtensionCompletionAlgebra w u |>.toSMul

local instance infinitePlaceLocalizedCompletionAlgebra :
    Algebra w.1.Completion u.1.Completion :=
  AbsoluteValue.completionAlgebra w.1 u.1 u.2

local instance infinitePlaceAllCompletionAlgebra
    (u' : AbsoluteValueExtension w.1 L) :
    Algebra w.1.Completion u'.1.Completion :=
  AbsoluteValue.completionAlgebra w.1 u'.1 u'.2

local instance infinitePlaceScalarTensorUnitsAction :
    MulDistribMulAction (L ≃ₐ[K] L) (w.Completion ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := w.Completion)

local instance infinitePlaceLocalTensorUnitsAction :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (LocalTensorAlgebra (L := L) w.1)ˣ :=
  localTensorUnitsAction (K := K) (L := L) w.1

omit [NumberField K] [NumberField L] in
/-- The actual archimedean local tensor equivalence is equivariant for the
full Galois action. -/
theorem
    infinitePlaceTensorUnitsEquivLocalPlaceBlock_smul
    (σ : L ≃ₐ[K] L)
    (z : (w.Completion ⊗[K] L)ˣ) :
    let :=
      decompositionGroupLocalUnitsAction w.1 hw u
    infinitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w hw u (σ • z) =
      σ •
        infinitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w hw u z := by
  intro sharedOwner1
  have hsource :
      infinitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) w (σ • z) =
        σ • infinitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) w z :=
    infinitePlaceLocalTensorUnitsEquiv_smul
      (K := K) (L := L) w σ z
  calc
    infinitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w hw u (σ • z) =
      localTensorUnitsEquivLocalPlaceBlock w.1 hw u
        (σ • infinitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) w z) :=
      congrArg
        (localTensorUnitsEquivLocalPlaceBlock w.1 hw u)
        hsource
    _ =
      σ • infinitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w hw u z :=
      localTensorUnitsEquivLocalPlaceBlock_smul
        w.1 hw u σ
        (infinitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) w z)

end Equivariance

end Galois
