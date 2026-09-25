/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.OpenNormalArithmeticStage
import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion

set_option autoImplicit false
/-!
# Chosen finite-place completions of an unramified arithmetic stage

The stage's everywhere-unramified certificate applies at the actual global centre
of the chosen finite-place extension. The ideal-to-completion comparison therefore
supplies unramifiedness for the chosen local completion, without a new local hypothesis.
-/

open scoped NumberField

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet ProCGroups IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- Every chosen finite-place completion of the arithmetic stage is unramified. -/
theorem openNormalArithmeticStage_chosenFinitePlaceIsUnramified
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (v : HeightOneSpectrum (𝓞 F)) :
    ChosenFinitePlaceIsUnramified
      (K := F) (L := (openNormalArithmeticStage F p hpOdd U).field) v := by
  apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt
  exact (openNormalArithmeticStage F p hpOdd U).everywhereUnramified.finitePlaces _

end ClassFieldTower.Martinet.Shafarevich
