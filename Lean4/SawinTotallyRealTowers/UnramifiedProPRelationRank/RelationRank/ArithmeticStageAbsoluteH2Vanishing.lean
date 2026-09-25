/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageKummerFieldUnitsH2
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerAbsoluteLift

set_option autoImplicit false
/-!
# Absolute degree-two vanishing at the unramified arithmetic stage

Over a base containing `mu_p`, the actual finite unramified stage supplies
a field-unit primitive through the supported-idele construction.  Hilbert
90 and the root correction turn this into an actual continuous lift of
the absolute Galois restriction to the cocycle extension.

Consequently every continuous degree-two class of the finite arithmetic
stage inflates to zero on the absolute Galois group.  The statements have
only the original arithmetic stage and primitive-root data as inputs.
A single local compactness proof unfolds the public absolute-group wrapper;
no data-bearing or global instance is introduced.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet ClassFieldTower.ProP ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime] (hpOdd : Odd (n : ℕ))
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))

/-- The actual arithmetic stage, repackaged as a finite Galois intermediate
field of the same chosen algebraic closure. -/
def openNormalArithmeticStageFiniteGaloisField :
    FiniteGaloisIntermediateField F (AlgebraicClosure F) where
  toIntermediateField := (openNormalArithmeticStage F (n : ℕ) hpOdd U).field
  finiteDimensional := (openNormalArithmeticStage F (n : ℕ) hpOdd U).finiteDimensional
  isGalois := (openNormalArithmeticStage F (n : ℕ) hpOdd U).isGalois

local notation "StageField" => FiniteEverywhereUnramifiedProPExtension.field
  (openNormalArithmeticStage F (n : ℕ) hpOdd U)

/-- Actual absolute-Galois restriction to the arithmetic stage. -/
def openNormalArithmeticStageAbsoluteRestriction :
    Field.absoluteGaloisGroup F →ₜ* Gal(StageField/F) :=
  absoluteFiniteGaloisRestriction F
    (openNormalArithmeticStageFiniteGaloisField F n hpOdd U)

/-- Every central mod-`p` cocycle extension at the unramified arithmetic
stage admits an actual continuous absolute-Galois lift. -/
theorem openNormalArithmeticStage_exists_absoluteLift
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (z : Cohomology.trivialZModPCocyclesLifted (n : ℕ) Gal(StageField/F) 2) :
    ∃ s : Field.absoluteGaloisGroup F →ₜ* H2CocycleExtension z,
      (H2CocycleExtension.projection z).comp s =
        openNormalArithmeticStageAbsoluteRestriction F n hpOdd U := by
  let E := openNormalArithmeticStageFiniteGaloisField F n hpOdd U
  let c := normalizedFiniteKummerTwoCocycle F n E z
  obtain ⟨b, hb⟩ := openNormalArithmeticStage_kummerTwoCocycle_isFieldUnitsCoboundary
    F n hpOdd U hmu c
  exact exists_absoluteLift_of_finiteKummerTwoCocycle_boundary F n E hmu z b hb

/-- Every degree-two class at the finite unramified arithmetic stage
vanishes after inflation to the absolute Galois group. -/
theorem openNormalArithmeticStage_absoluteH2Map_eq_zero
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (x : Cohomology.continuousCohomologyZModPLifted (n : ℕ) Gal(StageField/F) 2) :
    (Cohomology.continuousCohomologyZModPMapLifted (n : ℕ)
      (openNormalArithmeticStageAbsoluteRestriction F n hpOdd U) 2).hom x = 0 := by
  let : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F/F))
  obtain ⟨s, hs⟩ := openNormalArithmeticStage_exists_absoluteLift F n hpOdd U hmu
    (degreeTwoCocycleRepresentative x)
  rw [← degreeTwoCocycleRepresentative_π x]
  exact H2CocycleExtension.restriction_eq_zero_of_lift
    (openNormalArithmeticStageAbsoluteRestriction F n hpOdd U)
    (degreeTwoCocycleRepresentative x) s hs

end ClassFieldTower.Martinet.Shafarevich
