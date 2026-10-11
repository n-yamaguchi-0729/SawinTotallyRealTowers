/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianSeparableClosedTensor
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Extending automorphisms through the separable tensor comparison

The automorphism is transported from `id ⊗ σ` through the actual tensor
comparison. Its values on the chosen separable closure determine it, so
the resulting extension preserves composition.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

open scoped TensorProduct

variable {K : Type*} [Field K] (base : HenselianDVF K)
  {S E : Type*} [Field S] [Field E] [Algebra K S]
  [Algebra base.valuation.Completion E] [Algebra K E]
  [IsScalarTower K base.valuation.Completion E] [Algebra.IsSeparable K S]
  [IsSepClosed S] [Algebra.IsSeparable base.valuation.Completion E]

/-- Extend an automorphism of the embedded separable closure by tensoring
with the identity of the actual completion and transporting back to `E`. -/
def extendSeparableClosedAut (i : S →ₐ[K] E) (σ : S ≃ₐ[K] S) :
    E ≃ₐ[base.valuation.Completion] E :=
  (base.separableClosedTensorEquiv i).autCongr
    (Algebra.TensorProduct.congr (R := K) (S := base.valuation.Completion)
      (AlgEquiv.refl : base.valuation.Completion ≃ₐ[base.valuation.Completion]
        base.valuation.Completion) σ)

/-- Extension agrees with the original action through the chosen embedding. -/
@[simp] theorem extendSeparableClosedAut_apply (i : S →ₐ[K] E)
    (σ : S ≃ₐ[K] S) (s : S) :
    base.extendSeparableClosedAut i σ (i s) = i (σ s) := by
  let e : base.valuation.Completion ⊗[K] S ≃ₐ[base.valuation.Completion] E :=
    base.separableClosedTensorEquiv i
  have he (t : S) : e (1 ⊗ₜ[K] t) = i t := by
    change base.separableClosedTensorEquiv i (1 ⊗ₜ[K] t) = i t
    rw [separableClosedTensorEquiv_tmul, map_one, one_mul]
  change e ((Algebra.TensorProduct.congr
    (AlgEquiv.refl : base.valuation.Completion ≃ₐ[base.valuation.Completion]
      base.valuation.Completion) σ) (e.symm (i s))) = i (σ s)
  rw [← he s, e.symm_apply_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  exact he (σ s)

/-- The extension preserves composition of the original automorphisms. -/
theorem extendSeparableClosedAut_mul (i : S →ₐ[K] E) (σ τ : S ≃ₐ[K] S) :
    base.extendSeparableClosedAut i (σ * τ) =
      base.extendSeparableClosedAut i σ * base.extendSeparableClosedAut i τ := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.ext_of_adjoin_eq_top (base.toDVF.adjoin_range_eq_top_of_isSepClosed i)
  rintro x ⟨s, rfl⟩
  change base.extendSeparableClosedAut i (σ * τ) (i s) =
    base.extendSeparableClosedAut i σ (base.extendSeparableClosedAut i τ (i s))
  rw [extendSeparableClosedAut_apply, extendSeparableClosedAut_apply,
    extendSeparableClosedAut_apply]
  rfl

end ValuationTheory.DiscreteValuationField.HenselianDVF
