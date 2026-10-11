/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Padic.CyclotomicTeichmullerCharacter
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CyclotomicAutToPowRestriction

/-!
# Restriction compatibility of finite cyclotomic Teichmüller characters

The two characters on a cyclotomic extension and its base change agree
along the actual restriction homomorphism. Normality of the lower
cyclotomic extension supplies the restriction; no bijectivity or
compatibility of chosen primitive roots is assumed.
-/

namespace LocalFieldTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

variable (F K L E : Type*) [Field F] [Field K] [Field L] [Field E]
  [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K E] [Algebra L E]
  [IsScalarTower F K E] [IsScalarTower F L E] [Normal F K]
  (p : ℕ) [Fact p.Prime]
  [IsCyclotomicExtension {p} F K] [IsCyclotomicExtension {p} L E]

/-- The finite cyclotomic Teichmüller character agrees with the lower
character evaluated on the actual restricted automorphism. -/
theorem primeCyclotomicTeichmullerCharacter_restrictRestrictAlgEquivMapHom
    (σ : E ≃ₐ[L] E) :
    primeCyclotomicTeichmullerCharacter F K p
      (IntermediateField.restrictRestrictAlgEquivMapHom F K L E σ) =
      primeCyclotomicTeichmullerCharacter L E p σ := by
  change Examples.Qp.teichmullerUnits p
      ((IsCyclotomicExtension.zeta_spec p F K).autToPow F
        (IntermediateField.restrictRestrictAlgEquivMapHom F K L E σ)) =
    Examples.Qp.teichmullerUnits p ((IsCyclotomicExtension.zeta_spec p L E).autToPow L σ)
  rw [autToPow_restrictRestrictAlgEquivMapHom p
    (IsCyclotomicExtension.zeta_spec p F K) (IsCyclotomicExtension.zeta_spec p L E) σ]

/-- Equality of the actual character homomorphisms after restriction. -/
theorem primeCyclotomicTeichmullerCharacter_comp_restrictRestrictAlgEquivMapHom :
    (primeCyclotomicTeichmullerCharacter F K p).comp
      (IntermediateField.restrictRestrictAlgEquivMapHom F K L E) =
      primeCyclotomicTeichmullerCharacter L E p := by
  apply MonoidHom.ext
  intro σ
  exact primeCyclotomicTeichmullerCharacter_restrictRestrictAlgEquivMapHom F K L E p σ

end LocalFieldTheory.DiscreteValuationField
