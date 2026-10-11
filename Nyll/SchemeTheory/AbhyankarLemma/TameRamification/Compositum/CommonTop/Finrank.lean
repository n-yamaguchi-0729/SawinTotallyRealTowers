/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Compositum.CommonTop.BranchFinrank
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Compositum.CommonTop.LowerCanonical

/-!
# Finrank-coprime common-top endpoints

Total tameness converts field-degree coprimality into the lower-index
coprimality consumed by the common-top endpoints.
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

/-- Finrank-coprime common-top Abhyankar index bound. -/
theorem commonTop_rightCanonical_abhyankarIndexBound_of_lowerCanonical_totalTame_of_finrank_coprime
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
    AbhyankarIndexBound
      (ramificationIndex baseK.toDVF leftTarget.toDVF)
      (ramificationIndex baseK.toDVF base.toDVF)
      (ramificationIndex base.toDVF commonTarget.toDVF) :=
  commonTop_rightCanonical_abhyankarIndexBound_of_lowerCanonical_totalTame_of_coprime
    L K' hleft hbase
    (commonTop_lowerCanonicalRamificationIndex_coprime_of_totalTame_of_finrank_coprime
      L K' hleft hbase hcop)

omit [leftTarget.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Finrank-coprime right upper index-one endpoint. -/
theorem commonTop_right_ramificationIndex_eq_one_of_lower_totalTame_of_finrank_coprime_of_dvd
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K'))
    (hdiv :
      ramificationIndex baseK.toDVF leftTarget.toDVF ∣
        ramificationIndex baseK.toDVF base.toDVF) :
    ramificationIndex base.toDVF commonTarget.toDVF = 1 :=
  commonTop_rightCanonical_ramificationIndex_eq_one_of_lowerCanonical_totalTame_of_coprime_of_dvd
    L K' hleft hbase
    (commonTop_lowerCanonicalRamificationIndex_coprime_of_totalTame_of_finrank_coprime
      L K' hleft hbase hcop)
    hdiv

omit [leftTarget.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Finrank-coprime right upper unramified endpoint. -/
theorem commonTop_rightCanonical_isUnramified_of_lowerCanonical_totalTame_of_finrank_coprime_of_dvd
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K'))
    (hdiv :
      ramificationIndex baseK.toDVF leftTarget.toDVF ∣
        ramificationIndex baseK.toDVF base.toDVF) :
    IsUnramified base.toDVF commonTarget.toDVF :=
  commonTop_rightCanonical_isUnramified_of_lowerCanonical_totalTame_of_coprime_of_dvd
    L K' hleft hbase
    (commonTop_lowerCanonicalRamificationIndex_coprime_of_totalTame_of_finrank_coprime
      L K' hleft hbase hcop)
    hdiv

omit [leftTarget.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Finrank-coprime right upper tame endpoint. -/
theorem
  commonTop_rightCanonical_isTamelyRamified_of_lowerCanonical_totalTame_of_finrank_coprime_of_dvd
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K'))
    (hdiv :
      ramificationIndex baseK.toDVF leftTarget.toDVF ∣
        ramificationIndex baseK.toDVF base.toDVF)
    (hres : Algebra.IsSeparable base.residueField commonTarget.residueField) :
    IsTamelyRamified base.toDVF commonTarget.toDVF :=
  commonTop_rightCanonical_isTamelyRamified_of_lowerCanonical_totalTame_of_coprime_of_dvd
    L K' hleft hbase
    (commonTop_lowerCanonicalRamificationIndex_coprime_of_totalTame_of_finrank_coprime
      L K' hleft hbase hcop)
    hdiv hres

omit [base.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Finrank-coprime left upper index-one endpoint. -/
theorem commonTop_left_ramificationIndex_eq_one_of_lower_totalTame_of_finrank_coprime_of_dvd
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K'))
    (hdiv :
      ramificationIndex baseK.toDVF base.toDVF ∣
        ramificationIndex baseK.toDVF leftTarget.toDVF) :
    ramificationIndex leftTarget.toDVF commonTarget.toDVF = 1 :=
  commonTop_leftCanonical_ramificationIndex_eq_one_of_lowerCanonical_totalTame_of_coprime_of_dvd
    L K' hleft hbase
    (commonTop_lowerCanonicalRamificationIndex_coprime_of_totalTame_of_finrank_coprime
      L K' hleft hbase hcop)
    hdiv

omit [base.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Finrank-coprime left upper unramified endpoint. -/
theorem commonTop_leftCanonical_isUnramified_of_lowerCanonical_totalTame_of_finrank_coprime_of_dvd
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K'))
    (hdiv :
      ramificationIndex baseK.toDVF base.toDVF ∣
        ramificationIndex baseK.toDVF leftTarget.toDVF) :
    IsUnramified leftTarget.toDVF commonTarget.toDVF :=
  commonTop_leftCanonical_isUnramified_of_lowerCanonical_totalTame_of_coprime_of_dvd
    L K' hleft hbase
    (commonTop_lowerCanonicalRamificationIndex_coprime_of_totalTame_of_finrank_coprime
      L K' hleft hbase hcop)
    hdiv

omit [base.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Finrank-coprime left upper tame endpoint. -/
theorem
  commonTop_leftCanonical_isTamelyRamified_of_lowerCanonical_totalTame_of_finrank_coprime_of_dvd
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K'))
    (hdiv :
      ramificationIndex baseK.toDVF base.toDVF ∣
        ramificationIndex baseK.toDVF leftTarget.toDVF)
    (hres :
      Algebra.IsSeparable leftTarget.residueField commonTarget.residueField) :
    IsTamelyRamified leftTarget.toDVF commonTarget.toDVF :=
  commonTop_leftCanonical_isTamelyRamified_of_lowerCanonical_totalTame_of_coprime_of_dvd
    L K' hleft hbase
    (commonTop_lowerCanonicalRamificationIndex_coprime_of_totalTame_of_finrank_coprime
      L K' hleft hbase hcop)
    hdiv hres

end CommonTop

end FieldCompositum
end TameAbhyankar

end
