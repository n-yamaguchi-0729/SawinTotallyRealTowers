/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageChosenUnramified
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.UnramifiedKummerFieldUnitsH2

set_option autoImplicit false
/-!
# Field-unit primitives for Kummer classes at the arithmetic stage

The actual stage supplies its p-group Galois group and unramifiedness at
every place. The proved supported-idele construction and field-unit H²
injection therefore kill its Kummer H² classes and produce field-unit
primitives, ready for the Hilbert-90 and Kummer correction.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime] (hpOdd : Odd (n : ℕ))
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))
variable (hmu : (primitiveRoots (n : ℕ) F).Nonempty)

local notation "StageField" => FiniteEverywhereUnramifiedProPExtension.field
  (openNormalArithmeticStage F (n : ℕ) hpOdd U)

/-- Every Kummer H² class at the actual arithmetic stage vanishes in
the field-unit representation. -/
theorem openNormalArithmeticStage_kummerH2_eq_zero
    (x : groupCohomology
      (Rep.trivial ℤ Gal(StageField / F) (ULift (ZMod (n : ℕ)))) 2) :
    (finiteKummerCoefficientH2Map F StageField n hmu).hom x = 0 :=
  unramifiedFiniteKummerCoefficientH2Map_eq_zero F StageField n hmu
    (openNormalArithmeticStage F (n : ℕ) hpOdd U).isPGroup
    (openNormalArithmeticStage_chosenFinitePlaceIsUnramified F (n : ℕ) hpOdd U)
    (fun v ↦ (openNormalArithmeticStage F (n : ℕ) hpOdd U).everywhereUnramified.infinitePlaces.1
      (chosenInfinitePlaceAbove (L := StageField) v)) x

/-- A mod-p two-cocycle at the actual arithmetic stage has an actual
field-unit primitive after the chosen Kummer coefficient map. -/
theorem openNormalArithmeticStage_kummerTwoCocycle_isFieldUnitsCoboundary
    (c : groupCohomology.cocycles₂
      (Rep.trivial ℤ Gal(StageField / F) (ULift (ZMod (n : ℕ))))) :
    ∃ b : Gal(StageField / F) → Additive StageFieldˣ,
      (groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits F StageField)).hom b =
        (groupCohomology.mapCocycles₂ (MonoidHom.id Gal(StageField / F))
          (finiteKummerCoefficientRepHom F StageField n hmu) c).1 :=
  unramifiedFiniteKummerTwoCocycle_isFieldUnitsCoboundary F StageField n hmu
    (openNormalArithmeticStage F (n : ℕ) hpOdd U).isPGroup
    (openNormalArithmeticStage_chosenFinitePlaceIsUnramified F (n : ℕ) hpOdd U)
    (fun v ↦ (openNormalArithmeticStage F (n : ℕ) hpOdd U).everywhereUnramified.infinitePlaces.1
      (chosenInfinitePlaceAbove (L := StageField) v)) c

end ClassFieldTower.Martinet.Shafarevich
