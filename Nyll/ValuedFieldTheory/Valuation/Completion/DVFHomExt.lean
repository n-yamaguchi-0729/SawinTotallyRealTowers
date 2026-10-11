/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.DVFTensorMap
import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Homomorphisms out of finite extension completions

The actual tensor map onto an extension completion makes a homomorphism
over the base completion determined by its values on the original field.
-/


namespace ValuationTheory.DiscreteValuationField.DVF

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (base : DVF K) (target : DVF L)
  [hExtension : base.valuation.HasExtension target.valuation]

/-- Homomorphisms from a finite extension completion over the base completion
are equal if they agree on the original extension field. -/
theorem completionAlgHom_ext [FiniteDimensional K L]
    {B : Type*} [CommRing B] [Algebra base.valuation.Completion B]
    (f g : @AlgHom base.valuation.Completion target.valuation.Completion B _ _ _
      (completionAlgebra base target) _)
    (h : ∀ l : L, f (l : target.valuation.Completion) = g (l : target.valuation.Completion)) :
    f = g := by
  let : Algebra base.valuation.Completion target.valuation.Completion :=
    completionAlgebra base target
  apply AlgHom.ext
  intro x
  obtain ⟨z, rfl⟩ := completionTensorHom_surjective base target x
  induction z using TensorProduct.inductionOn with
  | tmul a l =>
      rw [completionTensorHom_tmul, map_mul, map_mul]
      have hf : f (completionMap base target a) = algebraMap base.valuation.Completion B a :=
        f.commutes a
      have hg : g (completionMap base target a) = algebraMap base.valuation.Completion B a :=
        g.commutes a
      rw [hf, hg, h l]
  | add z w hz hw => simp only [map_add, hz, hw]

end ValuationTheory.DiscreteValuationField.DVF
