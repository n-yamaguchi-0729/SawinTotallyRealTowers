/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.RingTheory.TensorProduct.Maps
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
public import Nyll.ValuedFieldTheory.Valuation.Completion.TensorProductDecomposition

/-!
# Infinite-place completion and tensor comparisons
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable section



open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The wrapper completion at an infinite place as a `K`-algebra
equivalence with the underlying absolute-value completion. -/
def infinitePlaceCompletionAlgEquiv
    (w : InfinitePlace K) :
    w.Completion ≃ₐ[K] w.1.Completion :=
  AlgEquiv.refl

omit [NumberField L] in
/-- The canonical comparisons from concrete infinite-place completions to
absolute-value completions commute with the completion maps in a tower of
number fields. -/
theorem infinitePlaceCompletionAlgEquiv_algebraMap
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    let _ : w.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
    let u : AbsoluteValueExtension v.1 L :=
      ⟨w.1, fun x =>
        congrArg (fun q : InfinitePlace K => q.1 x) hw⟩
    let _ : Algebra v.1.Completion u.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 u.1 u.2
    RingHom.comp
        (algebraMap v.1.Completion u.1.Completion)
        (infinitePlaceCompletionAlgEquiv v).toRingEquiv =
      RingHom.comp
        (infinitePlaceCompletionAlgEquiv w).toRingEquiv
        (algebraMap v.Completion w.Completion) := by
  intro hLiesOver u completionAlgebra
  apply RingHom.ext
  intro x
  rfl

/-- Base change of the first tensor factor from the concrete
archimedean completion to the absolute-value completion. -/
noncomputable def infinitePlaceLocalTensorAlgEquiv
    (w : InfinitePlace K) :
    w.Completion ⊗[K] L ≃ₐ[K]
      (w.1.Completion ⊗[K] L) :=
  Algebra.TensorProduct.congr
    (infinitePlaceCompletionAlgEquiv w)
    (AlgEquiv.refl : L ≃ₐ[K] L)

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- The concrete-to-absolute completion comparison acts componentwise
on a pure tensor. -/
@[simp]
theorem infinitePlaceLocalTensorAlgEquiv_tmul
    (w : InfinitePlace K) (a : w.Completion) (x : L) :
    infinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) w (a ⊗ₜ[K] x) =
      infinitePlaceCompletionAlgEquiv w a ⊗ₜ[K] x := by
  rfl

/-- The induced multiplicative equivalence on local tensor units. -/
noncomputable def infinitePlaceLocalTensorUnitsEquiv
    (w : InfinitePlace K) :
    (w.Completion ⊗[K] L)ˣ ≃*
      ((w.1.Completion ⊗[K] L))ˣ :=
  Units.mapEquiv
    (infinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w).toMulEquiv
