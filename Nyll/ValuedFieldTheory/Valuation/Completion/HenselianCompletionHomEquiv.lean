/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.DVFHomExt
import Nyll.ValuedFieldTheory.Valuation.Completion.DVFHomExtension
import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianHomDescent
import Mathlib.Algebra.Algebra.Tower

/-!
# Correspondence of homomorphisms before and after completion

The actual extension map is bijective: the original field is embedded in
its completion, and separable elements descend uniquely to a Henselian
target. The inverse correspondence retains the original field embeddings.
-/

noncomputable section


namespace ValuationTheory.DiscreteValuationField.HenselianDVF

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  (base : HenselianDVF K) (targetL : DVF L) (targetM : DVF M)
  [hL : base.toDVF.valuation.HasExtension targetL.valuation]
  [hM : base.toDVF.valuation.HasExtension targetM.valuation]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [Algebra.IsAlgebraic K M]

local instance : UniformContinuousConstSMul K (WithVal targetL.valuation) :=
  WithVal.uniformContinuousConstSMul_algebra targetL.valuation

local instance : Algebra base.valuation.Completion targetL.valuation.Completion :=
  DVF.completionAlgebra base.toDVF targetL

/-- Extending homomorphisms to the actual completions is bijective for a
finite separable source and an algebraic target over a Henselian DVF. -/
theorem extendCompletionAlgHom_bijective :
    Function.Bijective (DVF.extendCompletionAlgHom base.toDVF targetL targetM) := by
  constructor
  · intro f g hfg
    apply AlgHom.ext
    intro x
    apply (DVF.toCompletionAlgHom (K := K) targetM).injective
    change (f x : targetM.valuation.Completion) = (g x : targetM.valuation.Completion)
    have hx := congrArg (fun φ => φ (x : targetL.valuation.Completion)) hfg
    rw [DVF.extendCompletionAlgHom_coe, DVF.extendCompletionAlgHom_coe] at hx
    exact hx
  · intro φ
    have : IsScalarTower K base.valuation.Completion targetL.valuation.Completion :=
      DVF.completion_isScalarTower base.toDVF targetL
    have : IsScalarTower K base.valuation.Completion targetM.valuation.Completion :=
      DVF.completion_isScalarTower base.toDVF targetM
    obtain ⟨f, hf, _⟩ := base.existsUnique_algHom_of_completionAlgHom
      targetL targetM (φ.restrictScalars K)
    refine ⟨f, ?_⟩
    apply DVF.completionAlgHom_ext base.toDVF targetL
    intro x
    rw [DVF.extendCompletionAlgHom_coe]
    exact hf x

/-- The actual correspondence between original and completed homomorphisms. -/
def completionAlgHomEquiv :
    (L →ₐ[K] M) ≃
      @AlgHom base.valuation.Completion targetL.valuation.Completion
        targetM.valuation.Completion _ _ _
        (DVF.completionAlgebra base.toDVF targetL)
        (DVF.completionAlgebra base.toDVF targetM) :=
  Equiv.ofBijective (DVF.extendCompletionAlgHom base.toDVF targetL targetM)
    (extendCompletionAlgHom_bijective base targetL targetM)

/-- The inverse correspondence is the original homomorphism obtained by descent. -/
@[simp] theorem completionAlgHomEquiv_symm_coe
    (φ : @AlgHom base.valuation.Completion targetL.valuation.Completion
      targetM.valuation.Completion _ _ _
      (DVF.completionAlgebra base.toDVF targetL)
      (DVF.completionAlgebra base.toDVF targetM)) (x : L) :
    ((completionAlgHomEquiv base targetL targetM).symm φ x :
        targetM.valuation.Completion) = φ (x : targetL.valuation.Completion) := by
  have hφ : DVF.extendCompletionAlgHom base.toDVF targetL targetM
      ((completionAlgHomEquiv base targetL targetM).symm φ) = φ :=
    (completionAlgHomEquiv base targetL targetM).apply_symm_apply φ
  calc
    ((completionAlgHomEquiv base targetL targetM).symm φ x :
        targetM.valuation.Completion) =
      DVF.extendCompletionAlgHom base.toDVF targetL targetM
        ((completionAlgHomEquiv base targetL targetM).symm φ)
          (x : targetL.valuation.Completion) :=
      (DVF.extendCompletionAlgHom_coe base.toDVF targetL targetM
        ((completionAlgHomEquiv base targetL targetM).symm φ) x).symm
    _ = φ (x : targetL.valuation.Completion) :=
      congrArg (fun ψ => ψ (x : targetL.valuation.Completion)) hφ

end ValuationTheory.DiscreteValuationField.HenselianDVF
