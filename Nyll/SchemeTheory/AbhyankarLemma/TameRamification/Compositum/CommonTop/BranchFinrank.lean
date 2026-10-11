/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Compositum.CommonTop.Branch

/-!
# Finrank-coprime common-top branch calculus

Field-degree coprimality supplies the lower ramification-index coprimality
used by the common-top branch theorems.
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

omit [FiniteDimensional K L] [FiniteDimensional K K']
  [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] in
/-- Lower total tameness converts field-degree coprimality into coprimality of
the lower ramification indices. -/
theorem commonTop_lowerCanonicalRamificationIndex_coprime_of_totalTame_of_finrank_coprime
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K')) :
    Nat.Coprime
      (ramificationIndex baseK.toDVF leftTarget.toDVF)
      (ramificationIndex baseK.toDVF base.toDVF) := by
  rw [hleft.ramificationIndex_eq_degree,
    hbase.ramificationIndex_eq_degree]
  exact hcop

section CommonTop

variable {commonTarget : CompleteDVF.{v, y} (L ⊔ K' : IntermediateField K Ω)}
variable [base.valuation.HasExtension commonTarget.valuation]
variable [leftTarget.valuation.HasExtension commonTarget.valuation]
variable [baseK.valuation.HasExtension commonTarget.valuation]

omit [leftTarget.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Finrank-coprime source for right common-top branch divisibility. -/
theorem commonTop_right_ramificationIndex_dvd_left_of_lower_totalTame_of_finrank_coprime
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K')) :
    ramificationIndex base.toDVF commonTarget.toDVF ∣
      ramificationIndex baseK.toDVF leftTarget.toDVF :=
  commonTop_right_ramificationIndex_dvd_left_of_lower_totalTame_of_coprime
    L K' hleft hbase
    (commonTop_lowerCanonicalRamificationIndex_coprime_of_totalTame_of_finrank_coprime
      L K' hleft hbase hcop)

omit [base.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Finrank-coprime source for left common-top branch divisibility. -/
theorem commonTop_left_ramificationIndex_dvd_baseChange_of_lower_totalTame_of_finrank_coprime
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K')) :
    ramificationIndex leftTarget.toDVF commonTarget.toDVF ∣
      ramificationIndex baseK.toDVF base.toDVF :=
  commonTop_left_ramificationIndex_dvd_baseChange_of_lower_totalTame_of_coprime
    L K' hleft hbase
    (commonTop_lowerCanonicalRamificationIndex_coprime_of_totalTame_of_finrank_coprime
      L K' hleft hbase hcop)

omit [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Finrank-coprime source for coprimality of the two common-top branch
ramification indices. -/
theorem commonTop_canonical_ramificationIndex_coprime_of_lowerCanonical_totalTame_of_finrank_coprime
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K')) :
    Nat.Coprime
      (ramificationIndex base.toDVF commonTarget.toDVF)
      (ramificationIndex leftTarget.toDVF commonTarget.toDVF) :=
  commonTop_canonical_ramificationIndex_coprime_of_lowerCanonical_totalTame_of_coprime
    L K' hleft hbase
    (commonTop_lowerCanonicalRamificationIndex_coprime_of_totalTame_of_finrank_coprime
      L K' hleft hbase hcop)

/-- Finrank-coprime source for the right common-top lcm product. -/
theorem
  commonTop_rightCanonical_lcmRamificationProduct_of_lowerCanonical_totalTame_of_finrank_coprime
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
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K')) :
    ramificationIndex baseK.toDVF base.toDVF *
        ramificationIndex base.toDVF commonTarget.toDVF =
      Nat.lcm
        (ramificationIndex baseK.toDVF leftTarget.toDVF)
        (ramificationIndex baseK.toDVF base.toDVF) :=
  commonTop_rightCanonical_lcmRamificationProduct_of_lowerCanonical_totalTame_of_coprime
    L K' hleft hbase
    (commonTop_lowerCanonicalRamificationIndex_coprime_of_totalTame_of_finrank_coprime
      L K' hleft hbase hcop)

end CommonTop

end FieldCompositum
end TameAbhyankar

end
