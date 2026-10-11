/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.PlaneCurves.MonicChange
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Monic normalization after a finite constant extension

For a finite ground field, a generic linear projection need not be defined
over the ground field itself.  Fried--Jarden therefore first passes to a
suitable finite constant extension.  This file develops that missing
constant-extension form of linear monic normalization.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace FiniteExtensionMonicNormalization

open AffinePlaneCurve MonicPlaneCurveProjection
open PlaneCurveMonicNormalization

universe u

variable {K : Type u} [Field K]

/--
After extending coefficients to an algebraic closure, a nonzero plane
equation admits a linear change with unit leading coefficient.
-/
theorem exists_algebraicClosure_linearChangeY_leadingCoeff_isUnit
    {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {f : BivariatePolynomial K} (hf : f ≠ 0) :
    ∃ c : Fin 1 → Ω,
      IsUnit
        (yPolynomial
          (linearChangeY c
            (MvPolynomial.map
              (algebraMap K Ω) f))).leadingCoeff := by
  let : IsAlgClosed Ω :=
    IsAlgClosure.isAlgClosed K
  have hfmap :
      MvPolynomial.map
          (algebraMap K Ω) f ≠ 0 := by
    simpa using
      (MvPolynomial.map_injective
        (algebraMap K Ω)
        (algebraMap K Ω).injective).ne hf
  exact exists_linearChangeY_leadingCoeff_isUnit hfmap

end FiniteExtensionMonicNormalization
end Chapter06
end FieldArithmetic
