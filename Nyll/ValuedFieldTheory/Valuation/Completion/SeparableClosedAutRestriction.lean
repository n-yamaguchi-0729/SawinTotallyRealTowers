/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosedRange
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Restriction to an embedded separable closure

An automorphism over the common base preserves an embedded separably closed
separable extension. Restricting both the automorphism and its inverse gives
an automorphism of that extension, compatible with the original embedding.
-/

noncomputable section

namespace ValuationTheory.Completion

variable {K S E : Type*} [Field K] [Field S] [Field E]
  [Algebra K S] [Algebra K E] [IsSepClosed S] [Algebra.IsSeparable K S]

private def restrictionHom (i : S →ₐ[K] E) (σ : E ≃ₐ[K] E) : S →ₐ[K] S :=
  i.equivFieldRange.symm.toAlgHom.comp
    ((σ.toAlgHom.comp i).codRestrict i.fieldRange.toSubalgebra fun s =>
      mem_fieldRange_of_isSeparable_of_isSepClosed i
        ((Algebra.IsSeparable.isSeparable K s).map
          (σ.toAlgHom.comp i) (σ.toAlgHom.comp i).injective))

private theorem restrictionHom_apply
    (i : S →ₐ[K] E) (σ : E ≃ₐ[K] E) (s : S) :
    i (restrictionHom i σ s) = σ (i s) := by
  let y : i.fieldRange :=
    ⟨σ (i s), mem_fieldRange_of_isSeparable_of_isSepClosed i
      ((Algebra.IsSeparable.isSeparable K s).map
        (σ.toAlgHom.comp i) (σ.toAlgHom.comp i).injective)⟩
  change (i.equivFieldRange (i.equivFieldRange.symm y) : E) = (y : E)
  exact congrArg (fun z : i.fieldRange => (z : E))
    (i.equivFieldRange.apply_symm_apply y)

/-- Restrict an automorphism over the base to an embedded separably closed
separable extension. No separability of the ambient field is required. -/
def separableClosedAutRestriction
    (i : S →ₐ[K] E) (σ : E ≃ₐ[K] E) : S ≃ₐ[K] S :=
  AlgEquiv.ofBijective (restrictionHom i σ) ⟨(restrictionHom i σ).injective, by
    intro s
    refine ⟨restrictionHom i σ.symm s, i.injective ?_⟩
    change i (restrictionHom i σ (restrictionHom i σ.symm s)) = i s
    rw [restrictionHom_apply, restrictionHom_apply, σ.apply_symm_apply]⟩

/-- The restricted automorphism acts through the original embedding. -/
@[simp] theorem separableClosedAutRestriction_apply
    (i : S →ₐ[K] E) (σ : E ≃ₐ[K] E) (s : S) :
    i (separableClosedAutRestriction i σ s) = σ (i s) :=
  restrictionHom_apply i σ s

end ValuationTheory.Completion
