/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DyadicNormObstruction
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Normalized
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.RamificationIndex

/-!
# Dyadic quadratic norm forms

The normalized valuation and its uniformizer are constructed from the original
valuation ring. Thus the norm obstruction needs only the Henselian discrete
valuation and residue characteristic two.
-/

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

universe u v

/-- Every nontrivial quadratic square class over a Henselian dyadic DVF has a norm
outside the two square classes that become squares in the quadratic extension. -/
theorem exists_quadraticForm_outside_squareClasses
    {K : Type u} [Field K] [CharZero K]
    (base : HenselianDVF.{u, v} K) [CharP base.residueField 2]
    (a : K) (ha : ¬ IsSquare a) :
    ∃ x y : K, ¬ IsSquare (x ^ 2 - a * y ^ 2) ∧
      ¬ IsSquare ((x ^ 2 - a * y ^ 2) / a) := by
  obtain ⟨w, _, hring, π, hπ⟩ := base.toDVF.exists_normalized_valuation_with_uniformizer
  let P : ValuationSubring K → Prop := fun V =>
    HenselianRing V (IsLocalRing.maximalIdeal V)
  have hP : P base.valuation.valuationSubring := base.henselianRing
  have : HenselianRing w.valuationSubring (IsLocalRing.maximalIdeal w.valuationSubring) :=
    hring.symm ▸ hP
  let C : ValuationSubring K → Prop := fun V => CharP (IsLocalRing.ResidueField V) 2
  have hC : C base.valuation.valuationSubring := inferInstance
  have : CharP (IsLocalRing.ResidueField w.valuationSubring) 2 := hring.symm ▸ hC
  exact ValuationTheory.exists_quadraticForm_outside_squareClasses
    w (w.natCast_residueChar_lt_one 2) a π hπ ha

end ValuationTheory.DiscreteValuationField.HenselianDVF
