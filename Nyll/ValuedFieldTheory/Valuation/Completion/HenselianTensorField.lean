/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianPolynomialFactors
import Nyll.ValuedFieldTheory.Valuation.Completion.BaseChangeAdjoinRoot
import Mathlib.Algebra.Field.Equiv
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Finite separable extensions after completing a Henselian DVF

The minimal polynomial of a primitive element remains irreducible over the
actual valuation completion. The adjoined-root presentation of scalar
extension therefore makes the tensor product a field.
-/

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

universe u v w

open scoped TensorProduct

variable {K : Type u} [Field K]

/-- Completing a Henselian discretely valued field preserves the field
property of every finite separable scalar extension. -/
theorem completionTensor_isField (base : HenselianDVF.{u, v} K)
    (L : Type w) [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsField (base.valuation.Completion ⊗[K] L) := by
  let pb : PowerBasis K L := Field.powerBasisOfFiniteOfSeparable K L
  let q : Polynomial base.valuation.Completion :=
    (minpoly K pb.gen).map (algebraMap K base.valuation.Completion)
  have hq : Irreducible q := base.irreducible_map_completion
    (Algebra.IsSeparable.isSeparable K pb.gen) (minpoly.irreducible pb.isIntegral_gen)
  have : Fact (Irreducible q) := ⟨hq⟩
  exact MulEquiv.isField (Field.toIsField (AdjoinRoot q))
    (Completion.baseChangeEquivAdjoinRoot
      (A := base.valuation.Completion) pb).toRingEquiv.toMulEquiv

end ValuationTheory.DiscreteValuationField.HenselianDVF
