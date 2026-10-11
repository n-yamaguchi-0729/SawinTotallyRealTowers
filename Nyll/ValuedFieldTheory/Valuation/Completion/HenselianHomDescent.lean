/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.DVFTensorMap
import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianDVF
import Nyll.ValuedFieldTheory.Valuation.Completion.WithValScalars
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Henselian
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.FieldTheory.Separable

/-!
# Descending homomorphisms between valuation completions

The image of a separable element under a homomorphism of completions is
separable over the target field. Henselianity places that image in the
original target field, producing a unique homomorphism before completion.
-/


namespace ValuationTheory.DiscreteValuationField.HenselianDVF

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  (base : HenselianDVF K) (targetL : DVF L) (targetM : DVF M)
  [hM : base.toDVF.valuation.HasExtension targetM.valuation]

local instance : UniformContinuousConstSMul K (WithVal targetL.valuation) :=
  WithVal.uniformContinuousConstSMul_algebra targetL.valuation

include hM

/-- A homomorphism between the actual valuation completions over the original
ground field restricts uniquely to the original fields. Separability of the
source and algebraicity of the target suffice; neither extension is required
to be finite, and only the target valuation must extend the base valuation. -/
theorem existsUnique_algHom_of_completionAlgHom
    [Algebra.IsSeparable K L] [Algebra.IsAlgebraic K M]
    (φ : targetL.valuation.Completion →ₐ[K] targetM.valuation.Completion) :
    ∃! ψ : L →ₐ[K] M, ∀ x : L,
      DVF.toCompletionAlgHom (K := K) targetM (ψ x) =
        φ (DVF.toCompletionAlgHom (K := K) targetL x) := by
  let iL : L →ₐ[K] targetL.valuation.Completion := DVF.toCompletionAlgHom targetL
  let iM : M →ₐ[K] targetM.valuation.Completion := DVF.toCompletionAlgHom targetM
  let f : L →ₐ[K] targetM.valuation.Completion := φ.comp iL
  let htarget : HenselianDVF M :=
    { toDVF := targetM, instHenselian := base.henselianRing_of_hasExtension targetM }
  have hrange : ∀ x : L, f x ∈ iM.range := by
    intro x
    have hx : IsSeparable K (f x) :=
      (Algebra.IsSeparable.isSeparable K x).map f f.injective
    obtain ⟨y, hy⟩ := htarget.exists_completion_eq_of_isSeparable (f x) (hx.tower_top M)
    exact ⟨y, hy⟩
  let e : M ≃ₐ[K] iM.range := AlgEquiv.ofInjectiveField iM
  let f₀ : L →ₐ[K] iM.range := f.codRestrict iM.range hrange
  let ψ : L →ₐ[K] M := e.symm.toAlgHom.comp f₀
  have hψ : ∀ x : L, iM (ψ x) = f x := by
    intro x
    change (e (e.symm (f₀ x)) : targetM.valuation.Completion) = f x
    exact congrArg Subtype.val (e.apply_symm_apply (f₀ x))
  refine ⟨ψ, hψ, ?_⟩
  intro ψ' hψ'
  apply AlgHom.ext
  intro x
  apply iM.injective
  exact (hψ' x).trans (hψ x).symm

end ValuationTheory.DiscreteValuationField.HenselianDVF
