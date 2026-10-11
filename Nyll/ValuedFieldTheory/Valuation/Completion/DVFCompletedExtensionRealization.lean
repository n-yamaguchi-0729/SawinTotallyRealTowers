/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.DVFFiniteExtensionDescent
import Nyll.ValuedFieldTheory.Valuation.Completion.DVFTensorMap
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Localization
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Realizing finite extensions as actual valuation completions

The descended intermediate field receives the discrete valuation of its
localized integral closure. The two actual tensor maps identify its
completion with the prescribed extension, preserving both embeddings.
-/


namespace ValuationTheory.DiscreteValuationField.DVF

open scoped TensorProduct

universe u v w

variable {K : Type u} [Field K] (base : DVF.{u, v} K)

private theorem completion_equiv_of_tensor_equiv
    {L E : Type*} [Field L] [Field E] [Algebra K L] [FiniteDimensional K L]
    [Algebra base.valuation.Completion E]
    (target : DVF L) [hExtension : base.valuation.HasExtension target.valuation]
    (e : base.valuation.Completion ⊗[K] L ≃ₐ[base.valuation.Completion] E) :
    ∃ c : @AlgEquiv base.valuation.Completion target.valuation.Completion E _ _ _
        (completionAlgebra base target) _,
      ∀ x : L, c (x : target.valuation.Completion) = e (1 ⊗ₜ[K] x) := by
  let : Algebra base.valuation.Completion target.valuation.Completion :=
    completionAlgebra base target
  let h : E →ₐ[base.valuation.Completion] target.valuation.Completion :=
    (completionTensorHom base target).comp e.symm.toAlgHom
  have hsurjective : Function.Surjective h :=
    (completionTensorHom_surjective base target).comp e.symm.surjective
  let c : E ≃ₐ[base.valuation.Completion] target.valuation.Completion :=
    AlgEquiv.ofBijective h ⟨h.injective, hsurjective⟩
  refine ⟨c.symm, ?_⟩
  intro x
  apply c.injective
  rw [c.apply_symm_apply]
  change (x : target.valuation.Completion) =
    completionTensorHom base target (e.symm (e (1 ⊗ₜ[K] x)))
  rw [e.symm_apply_apply, completionTensorHom_tmul, map_one, one_mul]

/-- A finite separable extension of a valuation completion is the actual
completion of a finite separable intermediate field with an extending DVF.
The isomorphism is over the base completion and fixes that intermediate field. -/
theorem exists_completed_extension_realization
    (E : Type w) [Field E] [Algebra base.valuation.Completion E]
    [Algebra K E] [IsScalarTower K base.valuation.Completion E]
    [FiniteDimensional base.valuation.Completion E]
    [Algebra.IsSeparable base.valuation.Completion E] :
    ∃ F : IntermediateField K E, FiniteDimensional K F ∧ Algebra.IsSeparable K F ∧
      ∃ target : DVF.{w, 0} F,
      ∃ hExtension : base.valuation.HasExtension target.valuation,
      ∃ e : @AlgEquiv base.valuation.Completion target.valuation.Completion E _ _ _
          (completionAlgebra (hExtension := hExtension) base target) _,
        ∀ x : F, e (x : target.valuation.Completion) = (x : E) := by
  obtain ⟨F, hfinite, hseparable, hbijective⟩ :=
    base.exists_finiteSeparable_completion_descent E
  obtain ⟨target, hExtension⟩ : ∃ target : DVF.{w, 0} F,
      base.valuation.HasExtension target.valuation :=
    ⟨FiniteExtensionLocalization.dvf base, FiniteExtensionLocalization.dvf_hasExtension base⟩
  let e : base.valuation.Completion ⊗[K] F ≃ₐ[base.valuation.Completion] E :=
    AlgEquiv.ofBijective (completionIntermediateFieldTensorHom base F) hbijective
  obtain ⟨c, hc⟩ := completion_equiv_of_tensor_equiv base target e
  refine ⟨F, hfinite, hseparable, target, hExtension, c, ?_⟩
  intro x
  rw [hc]
  change completionIntermediateFieldTensorHom base F (1 ⊗ₜ[K] x) = (x : E)
  rw [completionIntermediateFieldTensorHom_tmul, map_one, one_mul]

end ValuationTheory.DiscreteValuationField.DVF
