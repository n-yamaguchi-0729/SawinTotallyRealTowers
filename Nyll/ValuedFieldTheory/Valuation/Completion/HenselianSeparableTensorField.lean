/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.FiniteSubfieldTensor
import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianTensorField
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Separable algebraic extensions after Henselian completion

Each tensor element comes from a finite subextension. Inverting a nonzero
lift there and mapping the inverse back proves the field property without
assuming a comparison map is injective.
-/

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

open scoped TensorProduct

variable {K : Type*} [Field K]

/-- Completing a Henselian DVF preserves the field property of scalar
extension by any separable algebraic extension, including a separable closure. -/
theorem completionTensor_isField_of_isSeparable (base : HenselianDVF K)
    (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] :
    IsField (base.valuation.Completion ⊗[K] L) := by
  have : Nontrivial (base.valuation.Completion ⊗[K] L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      K base.valuation.Completion L (algebraMap K base.valuation.Completion).injective
      (algebraMap K L).injective
  refine
    { exists_pair_ne := exists_pair_ne (base.valuation.Completion ⊗[K] L)
      mul_comm := fun x y => mul_comm x y
      mul_inv_cancel := ?_ }
  intro z hz
  obtain ⟨F, hfinite, w, hw⟩ :=
    Completion.exists_finiteSubfield_tensor_lift (K := K)
      (A := base.valuation.Completion) z
  let m :=
    (Algebra.TensorProduct.map (R := K) (S := base.valuation.Completion)
      (A := base.valuation.Completion) (B := F) (C := base.valuation.Completion) (D := L)
      (AlgHom.id base.valuation.Completion base.valuation.Completion) F.val).toRingHom
  change m w = z at hw
  have hwne : w ≠ 0 := by
    intro hwzero
    exact hz (hw.symm.trans ((congrArg m hwzero).trans m.map_zero'))
  obtain ⟨w', hprod⟩ := (base.completionTensor_isField F).mul_inv_cancel hwne
  refine ⟨m w', ?_⟩
  rw [← hw]
  exact (m.map_mul' w w').symm.trans ((congrArg m hprod).trans m.map_one')

end ValuationTheory.DiscreteValuationField.HenselianDVF
