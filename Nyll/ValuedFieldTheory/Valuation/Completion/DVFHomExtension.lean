/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.DVFTensorMap
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Extending field homomorphisms to actual valuation completions

Scalar extension of the original homomorphism, transported through the
actual tensor comparison, gives a homomorphism over the base completion.
Only the source extension needs to be finite and separable.
-/

noncomputable section


namespace ValuationTheory.DiscreteValuationField.DVF

open scoped TensorProduct

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  (base : DVF K) (targetL : DVF L) (targetM : DVF M)
  [hL : base.valuation.HasExtension targetL.valuation]
  [hM : base.valuation.HasExtension targetM.valuation]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [HenselianRing base.valuationSubring base.maximalIdeal]

local instance : Algebra base.valuation.Completion targetL.valuation.Completion :=
  completionAlgebra base targetL

/-- Extending a homomorphism from a finite separable extension of a Henselian
DVF to the actual completions. The target extension need not be finite. -/
def extendCompletionAlgHom (f : L →ₐ[K] M) :
    @AlgHom base.valuation.Completion targetL.valuation.Completion
      targetM.valuation.Completion _ _ _
      (completionAlgebra base targetL) (completionAlgebra base targetM) :=
  (completionTensorHom base targetM).comp
    ((Algebra.TensorProduct.map (R := K) (S := base.valuation.Completion)
      (AlgHom.id base.valuation.Completion base.valuation.Completion) f).comp
      (completionTensorEquiv base targetL).symm.toAlgHom)

/-- The extended homomorphism agrees with the original homomorphism on its field. -/
@[simp] theorem extendCompletionAlgHom_coe (f : L →ₐ[K] M) (x : L) :
    extendCompletionAlgHom base targetL targetM f (x : targetL.valuation.Completion) =
      (f x : targetM.valuation.Completion) := by
  let c : base.valuation.Completion ⊗[K] L ≃ₐ[base.valuation.Completion]
      targetL.valuation.Completion := completionTensorEquiv base targetL
  have hx : c (1 ⊗ₜ[K] x) = (x : targetL.valuation.Completion) := by
    change completionTensorEquiv base targetL (1 ⊗ₜ[K] x) =
      (x : targetL.valuation.Completion)
    rw [completionTensorEquiv_tmul, map_one, one_mul]
  change completionTensorHom base targetM
    (Algebra.TensorProduct.map (R := K) (S := base.valuation.Completion)
      (AlgHom.id base.valuation.Completion base.valuation.Completion) f
      (c.symm (x : targetL.valuation.Completion))) = (f x : targetM.valuation.Completion)
  rw [← hx, c.symm_apply_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    completionTensorHom_tmul, map_one, one_mul]

end ValuationTheory.DiscreteValuationField.DVF
