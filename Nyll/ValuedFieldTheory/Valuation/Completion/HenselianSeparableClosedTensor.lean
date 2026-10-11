/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.DVFSeparableClosedTensor
import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianSeparableTensorField
import Mathlib.Algebra.Algebra.Equiv

/-!
# Comparing separable closures across Henselian completion

The actual tensor map is injective because its source is a field, and
surjective by descent of finite separable generators. In particular it
applies to the usual lift between the two separable closures.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

open scoped TensorProduct

variable {K : Type*} [Field K] (base : HenselianDVF K)
  {S E : Type*} [Field S] [Field E] [Algebra K S]
  [Algebra base.valuation.Completion E] [Algebra K E]
  [IsScalarTower K base.valuation.Completion E] [Algebra.IsSeparable K S]

/-- The tensor map of a separable extension of the Henselian base is
injective into any field containing the two specified embeddings. -/
theorem separableClosedTensorHom_injective (i : S →ₐ[K] E) :
    Function.Injective (base.toDVF.separableClosedTensorHom i) := by
  let : Field (base.valuation.Completion ⊗[K] S) :=
    (base.completionTensor_isField_of_isSeparable S).toField
  exact (base.toDVF.separableClosedTensorHom i).injective

/-- Scalar extension of a separably closed separable extension of `K` is
the given separable extension of its completion. The map retains the
chosen embedding, rather than taking an unrelated field isomorphism. -/
def separableClosedTensorEquiv [IsSepClosed S]
    [Algebra.IsSeparable base.valuation.Completion E] (i : S →ₐ[K] E) :
    base.valuation.Completion ⊗[K] S ≃ₐ[base.valuation.Completion] E :=
  AlgEquiv.ofBijective (base.toDVF.separableClosedTensorHom i)
    ⟨base.separableClosedTensorHom_injective i,
      base.toDVF.separableClosedTensorHom_surjective i⟩

/-- The comparison is the product of the actual completion embedding and
the chosen embedding of the separably closed field. -/
@[simp] theorem separableClosedTensorEquiv_tmul [IsSepClosed S]
    [Algebra.IsSeparable base.valuation.Completion E] (i : S →ₐ[K] E)
    (a : base.valuation.Completion) (s : S) :
    base.separableClosedTensorEquiv i (a ⊗ₜ[K] s) =
      algebraMap base.valuation.Completion E a * i s :=
  base.toDVF.separableClosedTensorHom_tmul i a s

end ValuationTheory.DiscreteValuationField.HenselianDVF
