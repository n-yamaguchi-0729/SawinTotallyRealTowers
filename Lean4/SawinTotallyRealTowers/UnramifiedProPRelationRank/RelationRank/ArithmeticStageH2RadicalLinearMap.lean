/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2AdditionDifference
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportDecompositionRadicalPairing
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceUnramifiedRadicalPairing
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.AbsoluteCharacterRadicalReciprocity
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
/-!
# Linearity of the actual arithmetic-stage radical obstruction

The local additivity defect agrees on inertia with one actual global
character. Global reciprocity annihilates that character on the ideal
radical, while unramified local changes do not affect the pairing. Thus
the chosen lifts give an additive obstruction. Additivity over the prime
field supplies scalar compatibility without any additional choices.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology BigOperators
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology ClassFieldTower.ProP ClassFieldTower.Martinet ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime] (hpOdd : Odd (n : ℕ))
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))

local instance stageRadicalLinearCanonicalZModAddCommGroup :
    AddCommGroup (ZMod (n : ℕ)) :=
  (ZMod.instField (n : ℕ)).toDivisionRing.toAddCommGroup

local notation "StageQuotient" => MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ) ⧸
  (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))
local notation "StageH2" => continuousCohomologyZModPLifted (n : ℕ) StageQuotient 2

local instance stageRadicalLinearTopology : TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance stageRadicalLinearDiscrete : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _
local instance stageRadicalLinearH1Module
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod (n : ℕ)) (ContinuousH1ZMod (p := (n : ℕ)) (G := G)) := continuousH1ZModModule

/-- The actual chosen-lift radical obstruction is additive. -/
theorem arithmeticStageH2RadicalFunctional_add (x y : StageH2) :
    arithmeticStageH2RadicalFunctional F n hpOdd U (x + y) =
      arithmeticStageH2RadicalFunctional F n hpOdd U x +
        arithmeticStageH2RadicalFunctional F n hpOdd U y := by
  let S := arithmeticStageH2UniformRamifiedPlaces F n hpOdd U
  let c : StageH2 → ∀ v : ↥S, ContinuousH1ZMod (p := (n : ℕ))
      (G := finitePlaceAbsoluteDecompositionGroup F v.1) :=
    fun z v => h1OfCharacter (arithmeticStageH2GlobalLocalDifferenceCharacter F n hpOdd U z v.1)
  let psi := arithmeticStageH2AdditionDifference F n hpOdd U x y
  let d : ∀ v : ↥S, ContinuousH1ZMod (p := (n : ℕ))
      (G := finitePlaceAbsoluteDecompositionGroup F v.1) :=
    fun v => h1OfCharacter (psi.comp (finitePlaceAbsoluteDecompositionInclusion F v.1))
  let P := finiteSupportDecompositionRadicalPairing F (n : ℕ) S
  have hg : P d = 0 :=
    absoluteCharacter_finiteSupport_radical_annihilator F n psi hpOdd S
      (arithmeticStageH2AdditionDifference_inertia_of_not_mem F n hpOdd U x y)
  have heq : P (c (x + y) - (c x + c y)) = P d := by
    ext a
    rw [finiteSupportDecompositionRadicalPairing_apply,
      finiteSupportDecompositionRadicalPairing_apply]
    apply Finset.sum_congr rfl
    intro v _
    apply finitePlaceDecompositionReciprocityPairing_idealRadical_eq_of_inertiaRestriction_eq
      F n v.1
    ext sigma
    exact arithmeticStageH2AdditionDifference_inertia F n hpOdd U x y v.1 sigma.toMul
  have h := heq.trans hg
  rw [map_sub, map_add, sub_eq_zero] at h
  exact h

/-- The zero class has zero radical obstruction. -/
theorem arithmeticStageH2RadicalFunctional_zero :
    arithmeticStageH2RadicalFunctional F n hpOdd U 0 = 0 := by
  have h := arithmeticStageH2RadicalFunctional_add F n hpOdd U 0 0
  rw [zero_add] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- The source-produced linear map from finite-stage H² to the ideal-radical dual. -/
def arithmeticStageH2RadicalLinearMap :
    StageH2 →ₗ[ZMod (n : ℕ)] Module.Dual (ZMod (n : ℕ)) (idealPowerRadicalModP F (n : ℕ)) :=
  AddMonoidHom.toZModLinearMap (n : ℕ)
    { toFun := arithmeticStageH2RadicalFunctional F n hpOdd U
      map_zero' := arithmeticStageH2RadicalFunctional_zero F n hpOdd U
      map_add' := arithmeticStageH2RadicalFunctional_add F n hpOdd U }

@[simp]
theorem arithmeticStageH2RadicalLinearMap_apply (x : StageH2) :
    arithmeticStageH2RadicalLinearMap F n hpOdd U x =
      arithmeticStageH2RadicalFunctional F n hpOdd U x := rfl

end ClassFieldTower.Martinet.Shafarevich
