/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Compositum.CommonTop.Branch

/-!
# Common-top prime obstructions

Prime divisors of a nontrivial common primitive quotient obstruct
coprimality of the two upper ramification indices.
-/

noncomputable section

universe u v x y z t

namespace TameAbhyankar
namespace FieldCompositum

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]

variable (L K' : IntermediateField K Ω)
variable [FiniteDimensional K L] [FiniteDimensional K K']
variable [Algebra.IsSeparable K L] [Algebra.IsSeparable K K']
variable {base : CompleteDVF.{v, x} K'}

variable {baseK : CompleteDVF.{u, z} K}
variable {leftTarget : CompleteDVF.{v, t} L}
variable [baseK.valuation.HasExtension leftTarget.valuation]
variable [baseK.valuation.HasExtension base.valuation]

section CommonTop

variable {commonTarget : CompleteDVF.{v, y} (L ⊔ K' : IntermediateField K Ω)}
variable [base.valuation.HasExtension commonTarget.valuation]
variable [leftTarget.valuation.HasExtension commonTarget.valuation]
variable [baseK.valuation.HasExtension commonTarget.valuation]

/-- If the right upper index is not its primitive lower value and the lower
left branch is totally tame, the shared quotient has a prime factor dividing
both upper indices. -/
theorem commonTop_exists_prime_commonPrimitiveObstruction_of_leftCanonical_totalTame_of_right_ne
    [IsScalarTower baseK.valuationSubring base.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hright_ne :
      ramificationIndex base.toDVF commonTarget.toDVF ≠
        ramificationIndex baseK.toDVF leftTarget.toDVF /
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF)) :
    ∃ commonQuotient,
      commonQuotient ≤
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF) ∧
        ramificationIndex base.toDVF commonTarget.toDVF =
          (ramificationIndex baseK.toDVF leftTarget.toDVF /
              Nat.gcd
                (ramificationIndex baseK.toDVF leftTarget.toDVF)
                (ramificationIndex baseK.toDVF base.toDVF)) *
            commonQuotient ∧
        ramificationIndex leftTarget.toDVF commonTarget.toDVF =
          (ramificationIndex baseK.toDVF base.toDVF /
              Nat.gcd
                (ramificationIndex baseK.toDVF leftTarget.toDVF)
                (ramificationIndex baseK.toDVF base.toDVF)) *
            commonQuotient ∧
        ∃ p, Nat.Prime p ∧ p ∣ commonQuotient ∧
          p ∣ ramificationIndex base.toDVF commonTarget.toDVF ∧
          p ∣ ramificationIndex leftTarget.toDVF commonTarget.toDVF := by
  have hleft_pos :
      0 < ramificationIndex baseK.toDVF leftTarget.toDVF := by
    let : Module.IsTorsionFree baseK.valuationSubring
        leftTarget.valuationSubring :=
      moduleIsTorsionFree_target_valuationSubring_of_finite_separable
        baseK leftTarget
    exact
      LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_pos
        baseK leftTarget
  have hbase_pos :
      0 < ramificationIndex baseK.toDVF base.toDVF := by
    let : Module.IsTorsionFree baseK.valuationSubring base.valuationSubring :=
      moduleIsTorsionFree_target_valuationSubring_of_finite_separable
        baseK base
    exact
      LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_pos
        baseK base
  have hright_le :
      ramificationIndex base.toDVF commonTarget.toDVF ≤
        ramificationIndex baseK.toDVF leftTarget.toDVF := by
    rw [hleft.ramificationIndex_eq_degree]
    exact le_trans
      (open _root_.LocalFieldTheory.DiscreteValuationField.ValuedExtension in
        ramificationIndex_le_degree_of_finite_separable base commonTarget)
      (by
        change Module.finrank K' (L ⊔ K' : IntermediateField K Ω) ≤
          Module.finrank K L
        exact
          DiscreteValuationField.FieldCompositum.sup_finrank_over_right_le_left
            L K')
  exact
    TameAbhyankar.exists_prime_commonPrimitiveObstruction_of_mul_eq_mul_of_right_le_of_ne
      hleft_pos hbase_pos (commonTop_ramificationIndex_square L K')
      hright_le hright_ne

/-- Right upper non-primitiveity contradicts coprimality of the upper
branches. -/
theorem commonTop_not_coprime_upperBranches_of_leftCanonical_totalTame_of_right_ne
    [IsScalarTower baseK.valuationSubring base.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hright_ne :
      ramificationIndex base.toDVF commonTarget.toDVF ≠
        ramificationIndex baseK.toDVF leftTarget.toDVF /
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF)) :
    ¬ Nat.Coprime
      (ramificationIndex base.toDVF commonTarget.toDVF)
      (ramificationIndex leftTarget.toDVF commonTarget.toDVF) := by
  intro hcop
  rcases
      commonTop_exists_prime_commonPrimitiveObstruction_of_leftCanonical_totalTame_of_right_ne
        L K' hleft hright_ne with
    ⟨_, _, _, _, p, hp, _, hp_right, hp_left⟩
  have hp_eq_one : p = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hp_right hp_left
  exact hp.not_dvd_one (by rw [hp_eq_one])

/-- Left upper non-primitiveity gives the same obstruction when the lower
left branch is totally tame. -/
theorem commonTop_not_coprime_upperBranches_of_leftCanonical_totalTame_of_left_ne
    [IsScalarTower baseK.valuationSubring base.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hleftTop_ne :
      ramificationIndex leftTarget.toDVF commonTarget.toDVF ≠
        ramificationIndex baseK.toDVF base.toDVF /
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF)) :
    ¬ Nat.Coprime
      (ramificationIndex base.toDVF commonTarget.toDVF)
      (ramificationIndex leftTarget.toDVF commonTarget.toDVF) := by
  have hright_ne :
      ramificationIndex base.toDVF commonTarget.toDVF ≠
        ramificationIndex baseK.toDVF leftTarget.toDVF /
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF) :=
    (commonTop_rightNePrimitive_iff_leftNePrimitive_of_ramificationIndex_square
      L K').mpr hleftTop_ne
  exact
    commonTop_not_coprime_upperBranches_of_leftCanonical_totalTame_of_right_ne
      L K' hleft hright_ne

/-- Symmetric prime obstruction extracted from the left upper branch when the
lower base-change branch is totally tame. -/
theorem
  commonTop_exists_prime_commonPrimitiveObstruction_of_baseChangeCanonical_totalTame_of_left_ne
    [IsScalarTower baseK.valuationSubring base.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hleftTop_ne :
      ramificationIndex leftTarget.toDVF commonTarget.toDVF ≠
        ramificationIndex baseK.toDVF base.toDVF /
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF)) :
    ∃ commonQuotient,
      commonQuotient ≤
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF) ∧
        ramificationIndex base.toDVF commonTarget.toDVF =
          (ramificationIndex baseK.toDVF leftTarget.toDVF /
              Nat.gcd
                (ramificationIndex baseK.toDVF leftTarget.toDVF)
                (ramificationIndex baseK.toDVF base.toDVF)) *
            commonQuotient ∧
        ramificationIndex leftTarget.toDVF commonTarget.toDVF =
          (ramificationIndex baseK.toDVF base.toDVF /
              Nat.gcd
                (ramificationIndex baseK.toDVF leftTarget.toDVF)
                (ramificationIndex baseK.toDVF base.toDVF)) *
            commonQuotient ∧
        ∃ p, Nat.Prime p ∧ p ∣ commonQuotient ∧
          p ∣ ramificationIndex base.toDVF commonTarget.toDVF ∧
          p ∣ ramificationIndex leftTarget.toDVF commonTarget.toDVF := by
  have hleft_pos :
      0 < ramificationIndex baseK.toDVF leftTarget.toDVF := by
    let : Module.IsTorsionFree baseK.valuationSubring
        leftTarget.valuationSubring :=
      moduleIsTorsionFree_target_valuationSubring_of_finite_separable
        baseK leftTarget
    exact
      LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_pos
        baseK leftTarget
  have hbase_pos :
      0 < ramificationIndex baseK.toDVF base.toDVF := by
    let : Module.IsTorsionFree baseK.valuationSubring base.valuationSubring :=
      moduleIsTorsionFree_target_valuationSubring_of_finite_separable
        baseK base
    exact
      LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_pos
        baseK base
  have hleftTop_le :
      ramificationIndex leftTarget.toDVF commonTarget.toDVF ≤
        ramificationIndex baseK.toDVF base.toDVF := by
    rw [hbase.ramificationIndex_eq_degree]
    exact le_trans
      (open _root_.LocalFieldTheory.DiscreteValuationField.ValuedExtension in
        ramificationIndex_le_degree_of_finite_separable leftTarget commonTarget)
      (by
        change Module.finrank L (L ⊔ K' : IntermediateField K Ω) ≤
          Module.finrank K K'
        exact
          TameAbhyankar.FieldCompositum.sup_finrank_over_left_le_right L K')
  exact
    TameAbhyankar.exists_prime_commonPrimitiveObstruction_of_mul_eq_mul_of_left_le_of_ne
      hleft_pos hbase_pos (commonTop_ramificationIndex_square L K')
      hleftTop_le hleftTop_ne

/-- Left upper non-primitiveity contradicts upper-branch coprimality when the
lower base-change branch is totally tame. -/
theorem commonTop_not_coprime_upperBranches_of_baseChangeCanonical_totalTame_of_left_ne
    [IsScalarTower baseK.valuationSubring base.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hleftTop_ne :
      ramificationIndex leftTarget.toDVF commonTarget.toDVF ≠
        ramificationIndex baseK.toDVF base.toDVF /
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF)) :
    ¬ Nat.Coprime
      (ramificationIndex base.toDVF commonTarget.toDVF)
      (ramificationIndex leftTarget.toDVF commonTarget.toDVF) := by
  intro hcop
  rcases
      commonTop_exists_prime_commonPrimitiveObstruction_of_baseChangeCanonical_totalTame_of_left_ne
        L K' hbase hleftTop_ne with
    ⟨_, _, _, _, p, hp, _, hp_right, hp_left⟩
  have hp_eq_one : p = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hp_right hp_left
  exact hp.not_dvd_one (by rw [hp_eq_one])

/-- Right upper non-primitiveity gives the symmetric obstruction when the
lower base-change branch is totally tame. -/
theorem commonTop_not_coprime_upperBranches_of_baseChangeCanonical_totalTame_of_right_ne
    [IsScalarTower baseK.valuationSubring base.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hright_ne :
      ramificationIndex base.toDVF commonTarget.toDVF ≠
        ramificationIndex baseK.toDVF leftTarget.toDVF /
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF)) :
    ¬ Nat.Coprime
      (ramificationIndex base.toDVF commonTarget.toDVF)
      (ramificationIndex leftTarget.toDVF commonTarget.toDVF) := by
  have hleftTop_ne :
      ramificationIndex leftTarget.toDVF commonTarget.toDVF ≠
        ramificationIndex baseK.toDVF base.toDVF /
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF) :=
    (commonTop_rightNePrimitive_iff_leftNePrimitive_of_ramificationIndex_square
      L K').mp hright_ne
  exact
    commonTop_not_coprime_upperBranches_of_baseChangeCanonical_totalTame_of_left_ne
      L K' hbase hleftTop_ne

end CommonTop

end FieldCompositum
end TameAbhyankar

end
