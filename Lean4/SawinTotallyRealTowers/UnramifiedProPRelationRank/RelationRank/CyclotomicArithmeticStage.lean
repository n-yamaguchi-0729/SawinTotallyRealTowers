/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.OpenNormalArithmeticStage
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealRadicalCyclotomicBase
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.UnramifiedCompositumBaseChange

set_option autoImplicit false
/-!
# The actual cyclotomic base change of an unramified arithmetic stage

Inside the fixed algebraic closure of F, let C = F(μ_p) and let L be
the open-normal arithmetic stage. The field below is the actual compositum
C L, regarded as an intermediate field over C. Its two generator ranges
are proved to generate the top. Restriction therefore gives its p-group
Galois group and, by actual ideal-inertia restriction, finite-place
unramifiedness. Odd p supplies the infinite-place condition. No
unramifiedness of C/F is needed.

All instance choices are local and named. There is one new algebra
structure, the inclusion L → C L, and one matching original-base tower;
the C → C L tower is the canonical intermediate-field tower.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime] (hpOdd : Odd p)
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))

local notation "Cyclo" => IdealRadicalCyclotomicBase F p (Fact.out : p.Prime)
local notation "OriginalStage" => FiniteEverywhereUnramifiedProPExtension.field
  (openNormalArithmeticStage F p hpOdd U)

/-- The actual cyclotomic compositum C L inside the original algebraic closure. -/
def cyclotomicArithmeticStageField : IntermediateField Cyclo (AlgebraicClosure F) :=
  IntermediateField.extendScalars (show Cyclo ≤ Cyclo ⊔ OriginalStage from le_sup_left)

local notation "TopStage" => cyclotomicArithmeticStageField F p hpOdd U

local instance cyclotomicStageBaseFinite : FiniteDimensional F Cyclo :=
  finiteDimensional_idealRadicalCyclotomicBase F p Fact.out

local instance cyclotomicStageBaseNumber : NumberField Cyclo :=
  NumberField.of_module_finite F Cyclo

local instance cyclotomicStageFiniteOverOriginalBase : FiniteDimensional F TopStage := by
  change FiniteDimensional F ↥(Cyclo ⊔ OriginalStage)
  exact IntermediateField.finiteDimensional_sup Cyclo OriginalStage

/-- The compositum is a number field, with the original-base tower fixed. -/
theorem cyclotomicArithmeticStage_numberField : NumberField TopStage :=
  NumberField.of_module_finite F TopStage

attribute [local instance] cyclotomicArithmeticStage_numberField

/-- The actual compositum is finite dimensional over the cyclotomic base. -/
theorem cyclotomicArithmeticStage_finiteDimensional : FiniteDimensional Cyclo TopStage :=
  FiniteDimensional.right F Cyclo TopStage

attribute [local instance] cyclotomicArithmeticStage_finiteDimensional

/-- The original stage embeds into the actual cyclotomic compositum. -/
def cyclotomicArithmeticStageOriginalAlgHom : OriginalStage →ₐ[F] TopStage :=
  IntermediateField.inclusion (show OriginalStage ≤ Cyclo ⊔ OriginalStage from le_sup_right)

local instance cyclotomicStageOriginalAlgebra : Algebra OriginalStage TopStage :=
  (cyclotomicArithmeticStageOriginalAlgHom F p hpOdd U).toAlgebra

local instance cyclotomicStageOriginalTower : IsScalarTower F OriginalStage TopStage :=
  IsScalarTower.of_algebraMap_eq' (by ext; rfl)

/-- The original stage and the cyclotomic base generate the actual compositum. -/
theorem cyclotomicArithmeticStage_generatorRanges :
    (IsScalarTower.toAlgHom F OriginalStage TopStage).fieldRange ⊔
      (IsScalarTower.toAlgHom F Cyclo TopStage).fieldRange = ⊤ := by
  change IntermediateField.restrict (show OriginalStage ≤ Cyclo ⊔ OriginalStage from le_sup_right) ⊔
    IntermediateField.restrict (show Cyclo ≤ Cyclo ⊔ OriginalStage from le_sup_left) = ⊤
  apply IntermediateField.lift_injective (Cyclo ⊔ OriginalStage)
  rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
    IntermediateField.lift_restrict, IntermediateField.lift_top]
  exact sup_comm _ _

/-- Galoisness survives the actual cyclotomic base change. -/
theorem cyclotomicArithmeticStage_isGalois : IsGalois Cyclo TopStage := by
  let A := (IsScalarTower.toAlgHom F OriginalStage TopStage).fieldRange
  let B := (IsScalarTower.toAlgHom F Cyclo TopStage).fieldRange
  let eA := (IsScalarTower.toAlgHom F OriginalStage TopStage).equivFieldRange
  let eB := (IsScalarTower.toAlgHom F Cyclo TopStage).equivFieldRange
  let _ : IsGalois F A := IsGalois.of_algEquiv eA
  let _ : IsGalois B TopStage :=
    IsGalois.sup_right A B (cyclotomicArithmeticStage_generatorRanges F p hpOdd U)
  apply IsGalois.of_equiv_equiv (f := eB.symm.toRingEquiv) (g := RingEquiv.refl TopStage)
  apply RingHom.ext
  intro x
  exact congrArg (fun z : B ↦ (z : TopStage)) (eB.apply_symm_apply x)

local instance cyclotomicStageGalois : IsGalois Cyclo TopStage :=
  cyclotomicArithmeticStage_isGalois F p hpOdd U

/-- The actual base-changed Galois group embeds into the original p-group. -/
theorem cyclotomicArithmeticStage_isPGroup : IsPGroup p Gal(TopStage / Cyclo) :=
  compositumBaseChange_isPGroup F OriginalStage Cyclo TopStage
    (cyclotomicArithmeticStage_generatorRanges F p hpOdd U)
    (openNormalArithmeticStage F p hpOdd U).isPGroup

/-- The cyclotomic base change is unramified at every finite and infinite place,
without any unramifiedness assumption on the cyclotomic extension itself. -/
theorem cyclotomicArithmeticStage_everywhereUnramified : IsEverywhereUnramified Cyclo TopStage :=
  compositumBaseChange_everywhereUnramified F OriginalStage Cyclo TopStage hpOdd
    (cyclotomicArithmeticStage_generatorRanges F p hpOdd U)
    (openNormalArithmeticStage F p hpOdd U).isPGroup
    (openNormalArithmeticStage F p hpOdd U).everywhereUnramified.finitePlaces

end ClassFieldTower.Martinet.Shafarevich
