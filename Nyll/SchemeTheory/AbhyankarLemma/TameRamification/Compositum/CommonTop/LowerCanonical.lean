/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Compositum.CommonTop.Branch

/-!
# Lower-branch common-top Abhyankar consequences

This file exposes the common-top index-one, unramified, and tame endpoints
whose inputs are total tameness of the two lower valued extensions.
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

/-- Common-top Abhyankar index bound supplied by the lcm product for the
lower branches. -/
theorem commonTop_rightCanonical_abhyankarIndexBound_of_lowerCanonical_totalTame_of_coprime
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
    (hcop : Nat.Coprime
      (ramificationIndex baseK.toDVF leftTarget.toDVF)
      (ramificationIndex baseK.toDVF base.toDVF)) :
    AbhyankarIndexBound
      (ramificationIndex baseK.toDVF leftTarget.toDVF)
      (ramificationIndex baseK.toDVF base.toDVF)
      (ramificationIndex base.toDVF commonTarget.toDVF) := by
  have hbase_pos :
      0 < ramificationIndex baseK.toDVF base.toDVF := by
    let : Module.IsTorsionFree baseK.valuationSubring base.valuationSubring :=
      moduleIsTorsionFree_target_valuationSubring_of_finite_separable
        baseK base
    exact
      LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_pos
        baseK base
  exact abhyankarIndexBound_of_mul_eq_lcm hbase_pos
    (commonTop_rightCanonical_lcmRamificationProduct_of_lowerCanonical_totalTame_of_coprime
      L K' hleft hbase hcop)

omit [leftTarget.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- In the coprime lower-index case, lower divisibility forces the right upper
ramification index to be one. -/
theorem
  commonTop_rightCanonical_ramificationIndex_eq_one_of_lowerCanonical_totalTame_of_coprime_of_dvd
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime
      (ramificationIndex baseK.toDVF leftTarget.toDVF)
      (ramificationIndex baseK.toDVF base.toDVF))
    (hdiv :
      ramificationIndex baseK.toDVF leftTarget.toDVF ∣
        ramificationIndex baseK.toDVF base.toDVF) :
    ramificationIndex base.toDVF commonTarget.toDVF = 1 :=
  eq_one_of_dvd_of_dvd_of_coprime
    (commonTop_right_ramificationIndex_dvd_left_of_lower_totalTame_of_coprime
      L K' hleft hbase hcop)
    hdiv hcop

omit [leftTarget.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Right common-top unramified consequence. -/
theorem commonTop_rightCanonical_isUnramified_of_lowerCanonical_totalTame_of_coprime_of_dvd
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime
      (ramificationIndex baseK.toDVF leftTarget.toDVF)
      (ramificationIndex baseK.toDVF base.toDVF))
    (hdiv :
      ramificationIndex baseK.toDVF leftTarget.toDVF ∣
        ramificationIndex baseK.toDVF base.toDVF) :
    IsUnramified base.toDVF commonTarget.toDVF :=
  commonTop_rightCanonical_ramificationIndex_eq_one_of_lowerCanonical_totalTame_of_coprime_of_dvd
    L K' hleft hbase hcop hdiv

omit [leftTarget.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Tame form of the right common-top unramified consequence. -/
theorem commonTop_rightCanonical_isTamelyRamified_of_lowerCanonical_totalTame_of_coprime_of_dvd
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime
      (ramificationIndex baseK.toDVF leftTarget.toDVF)
      (ramificationIndex baseK.toDVF base.toDVF))
    (hdiv :
      ramificationIndex baseK.toDVF leftTarget.toDVF ∣
        ramificationIndex baseK.toDVF base.toDVF)
    (hres : Algebra.IsSeparable base.residueField commonTarget.residueField) :
    IsTamelyRamified base.toDVF commonTarget.toDVF :=
  isTamelyRamified_of_isUnramified_of_residue_isSeparable
    base commonTarget
    (commonTop_rightCanonical_isUnramified_of_lowerCanonical_totalTame_of_coprime_of_dvd
      L K' hleft hbase hcop hdiv)
    hres

omit [base.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Symmetric index-one consequence for the left upper branch. -/
theorem
  commonTop_leftCanonical_ramificationIndex_eq_one_of_lowerCanonical_totalTame_of_coprime_of_dvd
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime
      (ramificationIndex baseK.toDVF leftTarget.toDVF)
      (ramificationIndex baseK.toDVF base.toDVF))
    (hdiv :
      ramificationIndex baseK.toDVF base.toDVF ∣
        ramificationIndex baseK.toDVF leftTarget.toDVF) :
    ramificationIndex leftTarget.toDVF commonTarget.toDVF = 1 :=
  eq_one_of_dvd_of_dvd_of_coprime
    (commonTop_left_ramificationIndex_dvd_baseChange_of_lower_totalTame_of_coprime
      L K' hleft hbase hcop)
    hdiv hcop.symm

omit [base.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Left common-top unramified consequence. -/
theorem commonTop_leftCanonical_isUnramified_of_lowerCanonical_totalTame_of_coprime_of_dvd
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime
      (ramificationIndex baseK.toDVF leftTarget.toDVF)
      (ramificationIndex baseK.toDVF base.toDVF))
    (hdiv :
      ramificationIndex baseK.toDVF base.toDVF ∣
        ramificationIndex baseK.toDVF leftTarget.toDVF) :
    IsUnramified leftTarget.toDVF commonTarget.toDVF :=
  commonTop_leftCanonical_ramificationIndex_eq_one_of_lowerCanonical_totalTame_of_coprime_of_dvd
    L K' hleft hbase hcop hdiv

omit [base.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Tame form of the left common-top unramified consequence. -/
theorem commonTop_leftCanonical_isTamelyRamified_of_lowerCanonical_totalTame_of_coprime_of_dvd
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime
      (ramificationIndex baseK.toDVF leftTarget.toDVF)
      (ramificationIndex baseK.toDVF base.toDVF))
    (hdiv :
      ramificationIndex baseK.toDVF base.toDVF ∣
        ramificationIndex baseK.toDVF leftTarget.toDVF)
    (hres :
      Algebra.IsSeparable leftTarget.residueField commonTarget.residueField) :
    IsTamelyRamified leftTarget.toDVF commonTarget.toDVF :=
  isTamelyRamified_of_isUnramified_of_residue_isSeparable
    leftTarget commonTarget
    (commonTop_leftCanonical_isUnramified_of_lowerCanonical_totalTame_of_coprime_of_dvd
      L K' hleft hbase hcop hdiv)
    hres

end CommonTop

end FieldCompositum
end TameAbhyankar

end
