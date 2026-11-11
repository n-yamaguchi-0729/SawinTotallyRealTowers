/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport

/-!
# Generic evaluation core for transported reciprocity

This theorem works for an arbitrary finite abelian extension and subgroup
equality.  It proves the composition formula once without unfolding a
domain-specific selected-field construction.
-/



@[expose] public section

universe u v

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

attribute [local instance]
  globalNormResidueIdeleClassCommGroup
  globalNormResidueIdeleClassIsMulCommutative

variable
    {K : Type u} {L : Type v} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Evaluation of global reciprocity after continuous transport along an
equality between the actual norm range and a target subgroup. -/
theorem globalReciprocityContinuousMulEquiv_trans_quotientOfEq_apply
    (H : Subgroup (IdeleClassGroup K))
    (hNorm : (_root_.ideleClassNorm K L).range = H)
    (σ : Gal(L/K)) :
    ((globalReciprocityContinuousMulEquiv K L).trans
      (QuotientGroup.quotientContinuousMulEquivOfEq hNorm)) σ =
      QuotientGroup.quotientMulEquivOfEq hNorm
        (Additive.toMul
          ((globalNormResidueEquiv K L).symm
            (Additive.ofMul σ))) := by
  calc
    _ = QuotientGroup.quotientContinuousMulEquivOfEq hNorm
        (globalReciprocityContinuousMulEquiv K L σ) := rfl
    _ = QuotientGroup.quotientMulEquivOfEq hNorm
        (globalReciprocityContinuousMulEquiv K L σ) :=
      QuotientGroup.quotientContinuousMulEquivOfEq_apply _ _
    _ = _ :=
      congrArg
        (QuotientGroup.quotientMulEquivOfEq hNorm)
        (globalReciprocityContinuousMulEquiv_apply K L σ)

end GlobalClassFields
end GlobalClassFieldTheory
