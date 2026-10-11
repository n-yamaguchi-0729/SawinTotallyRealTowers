/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianSeparableAutExtension
import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosedAutRestriction
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Automorphism groups of separable closures across completion

Tensor extension and restriction through the chosen embedding are inverse.
The resulting group isomorphism retains the action on each embedded element.
No continuity or comparison theorem is assumed.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

variable {K : Type*} [Field K] (base : HenselianDVF K)
  {S E : Type*} [Field S] [Field E] [Algebra K S]
  [Algebra base.valuation.Completion E] [Algebra K E]
  [IsScalarTower K base.valuation.Completion E] [Algebra.IsSeparable K S]
  [IsSepClosed S] [Algebra.IsSeparable base.valuation.Completion E]

/-- The chosen embedding identifies the automorphism groups by actual
extension and restriction, with multiplication given by composition. -/
def separableClosedAutEquiv (i : S →ₐ[K] E) :
    (S ≃ₐ[K] S) ≃* (E ≃ₐ[base.valuation.Completion] E) where
  toFun := base.extendSeparableClosedAut i
  invFun σ := Completion.separableClosedAutRestriction i (σ.restrictScalars K)
  left_inv σ := by
    apply AlgEquiv.ext
    intro s
    apply i.injective
    change i (Completion.separableClosedAutRestriction i
      ((base.extendSeparableClosedAut i σ).restrictScalars K) s) = i (σ s)
    rw [Completion.separableClosedAutRestriction_apply]
    exact base.extendSeparableClosedAut_apply i σ s
  right_inv σ := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top (base.toDVF.adjoin_range_eq_top_of_isSepClosed i)
    rintro x ⟨s, rfl⟩
    change base.extendSeparableClosedAut i
      (Completion.separableClosedAutRestriction i (σ.restrictScalars K)) (i s) = σ (i s)
    rw [extendSeparableClosedAut_apply, Completion.separableClosedAutRestriction_apply]
    rfl
  map_mul' := base.extendSeparableClosedAut_mul i

/-- The group isomorphism intertwines the original field actions. -/
@[simp] theorem separableClosedAutEquiv_apply (i : S →ₐ[K] E)
    (σ : S ≃ₐ[K] S) (s : S) :
    base.separableClosedAutEquiv i σ (i s) = i (σ s) :=
  base.extendSeparableClosedAut_apply i σ s

/-- The inverse group isomorphism is restriction through the same embedding. -/
@[simp] theorem separableClosedAutEquiv_symm_apply (i : S →ₐ[K] E)
    (σ : E ≃ₐ[base.valuation.Completion] E) (s : S) :
    i ((base.separableClosedAutEquiv i).symm σ s) = σ (i s) :=
  Completion.separableClosedAutRestriction_apply i (σ.restrictScalars K) s

end ValuationTheory.DiscreteValuationField.HenselianDVF
