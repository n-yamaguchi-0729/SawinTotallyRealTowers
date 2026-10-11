/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.NormalSplittingPolynomial
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-!
# Cyclotomic extensions above finite normal extensions

Adjoining roots of unity to a finite normal extension preserves normality
over the original field. The upper field is the splitting field of the
product of a nonzero lower splitting polynomial and `X^n - 1`.
-/

namespace ValuationTheory.DiscreteValuationField

open Polynomial

/-- A cyclotomic extension above a finite normal extension is normal over
the bottom field, with no characteristic or valuation hypothesis. -/
theorem normal_cyclotomic_tower
    (F K E : Type*) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]
    [FiniteDimensional F K] [Normal F K]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} K E] : Normal F E := by
  obtain ⟨f, hf, hFK⟩ := Normal.exists_ne_zero_isSplittingField F K
  let g : F[X] := X ^ n - 1
  have hg : g ≠ 0 := X_pow_sub_C_ne_zero (NeZero.pos n) (1 : F)
  have hKE : IsSplittingField K E (g.map (algebraMap F K)) := by
    simpa only [g, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one] using
      (IsCyclotomicExtension.isSplittingField_X_pow_sub_one (n := n) (K := K) (L := E))
  have hFE : IsSplittingField F E (f * g) :=
    Polynomial.IsSplittingField.mul (F := F) (K := K) (L := E) f g hf hg
  exact Normal.of_isSplittingField (F := F) (E := E) (f * g)

end ValuationTheory.DiscreteValuationField
