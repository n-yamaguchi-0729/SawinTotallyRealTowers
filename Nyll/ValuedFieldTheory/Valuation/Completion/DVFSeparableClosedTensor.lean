/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.DVFSeparableClosedGeneration
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The tensor map from an embedded separably closed field

Multiplication of the two given embeddings is surjective because the
embedded separably closed field generates the separable extension of the
valuation completion. No Henselian hypothesis is used for surjectivity.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.DVF

open scoped TensorProduct

variable {K : Type*} [Field K] (base : DVF K)
  {S E : Type*} [Field S] [Field E] [Algebra K S]
  [Algebra base.valuation.Completion E] [Algebra K E]
  [IsScalarTower K base.valuation.Completion E]

/-- Multiplication of the completion embedding and a given `K`-embedding. -/
def separableClosedTensorHom (i : S →ₐ[K] E) :
    base.valuation.Completion ⊗[K] S →ₐ[base.valuation.Completion] E :=
  Algebra.TensorProduct.lift (Algebra.ofId base.valuation.Completion E) i
    (fun a s => Commute.all (algebraMap base.valuation.Completion E a) (i s))

/-- The actual tensor map preserves the specified embeddings. -/
@[simp] theorem separableClosedTensorHom_tmul (i : S →ₐ[K] E)
    (a : base.valuation.Completion) (s : S) :
    base.separableClosedTensorHom i (a ⊗ₜ[K] s) =
      algebraMap base.valuation.Completion E a * i s :=
  Algebra.TensorProduct.lift_tmul (Algebra.ofId base.valuation.Completion E) i
    (fun b t => Commute.all (algebraMap base.valuation.Completion E b) (i t)) a s

/-- A separably closed image generates the whole separable extension of
the completion, so its actual tensor map is surjective. -/
theorem separableClosedTensorHom_surjective [IsSepClosed S]
    [Algebra.IsSeparable base.valuation.Completion E] (i : S →ₐ[K] E) :
    Function.Surjective (base.separableClosedTensorHom i) := by
  apply (base.separableClosedTensorHom i).range_eq_top.mp
  apply top_unique
  rw [← base.adjoin_range_eq_top_of_isSepClosed i]
  apply Algebra.adjoin_le
  rintro x ⟨s, rfl⟩
  refine ⟨1 ⊗ₜ[K] s, ?_⟩
  change base.separableClosedTensorHom i (1 ⊗ₜ[K] s) = i s
  rw [separableClosedTensorHom_tmul, map_one, one_mul]

end ValuationTheory.DiscreteValuationField.DVF
