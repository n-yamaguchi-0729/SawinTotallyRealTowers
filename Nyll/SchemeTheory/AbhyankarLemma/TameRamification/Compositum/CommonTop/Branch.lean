/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValuedExtension.Tower
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValuedExtension.Canonical
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Compositum.Field
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Index

/-!
# Common-top branch calculus

This file contains the ramification-index square, branch divisibility
statements, and lower-branch lcm product used by the Abhyankar step.  All
invariants belong directly to the chosen valued fields; there are no
extension records or canonicalization constructors.
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

instance finiteDimensional_commonTop_over_base :
    FiniteDimensional K (L ⊔ K' : IntermediateField K Ω) :=
  IntermediateField.finiteDimensional_sup L K'

instance finiteDimensional_commonTop_over_right :
    FiniteDimensional K' (L ⊔ K' : IntermediateField K Ω) :=
  TameAbhyankar.FieldCompositum.finiteDimensional_sup_over_right L K'

instance finiteDimensional_commonTop_over_left :
    FiniteDimensional L (L ⊔ K' : IntermediateField K Ω) :=
  DiscreteValuationField.FieldCompositum.finiteDimensional_sup_over_left L K'

instance isSeparable_commonTop_over_right :
    Algebra.IsSeparable K' (L ⊔ K' : IntermediateField K Ω) :=
  TameAbhyankar.FieldCompositum.isSeparable_sup_over_right L K'

instance isSeparable_commonTop_over_left :
    Algebra.IsSeparable L (L ⊔ K' : IntermediateField K Ω) :=
  TameAbhyankar.FieldCompositum.isSeparable_sup_over_left L K'

omit [FiniteDimensional K L] [FiniteDimensional K K']
  [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] in
/-- Ramification-index products agree for the compositum square with common
top `L ⊔ K'`. -/
theorem commonTop_ramificationIndex_square
    [IsScalarTower baseK.valuationSubring base.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring
      commonTarget.valuationSubring] :
    ramificationIndex baseK.toDVF base.toDVF *
        ramificationIndex base.toDVF commonTarget.toDVF =
      ramificationIndex baseK.toDVF leftTarget.toDVF *
        ramificationIndex leftTarget.toDVF commonTarget.toDVF :=
  ramificationIndex_square
    (base := baseK.toDVF) (middle := base.toDVF)
    (leftMiddle := leftTarget.toDVF) (target := commonTarget.toDVF)

/-- The common-top ramification square factors both upper indices through the
primitive parts of the two lower indices, with one shared quotient. -/
theorem commonTop_exists_commonPrimitiveQuotient_of_ramificationIndex_square
    [IsScalarTower baseK.valuationSubring base.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)] :
    ∃ commonQuotient,
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
            commonQuotient := by
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
  exact exists_commonPrimitiveQuotient_of_mul_eq_mul
    hleft_pos hbase_pos (commonTop_ramificationIndex_square L K')

/-- In the common-top square, the two upper branches are primitive at the same
time. -/
theorem commonTop_rightPrimitive_iff_leftPrimitive_of_ramificationIndex_square
    [IsScalarTower baseK.valuationSubring base.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)] :
    Iff
      (ramificationIndex base.toDVF commonTarget.toDVF =
        ramificationIndex baseK.toDVF leftTarget.toDVF /
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF))
      (ramificationIndex leftTarget.toDVF commonTarget.toDVF =
        ramificationIndex baseK.toDVF base.toDVF /
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF)) := by
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
  exact right_eq_div_gcd_iff_left_eq_div_gcd_of_mul_eq_mul
    hleft_pos hbase_pos (commonTop_ramificationIndex_square L K')

/-- Contrapositive form of
`commonTop_rightPrimitive_iff_leftPrimitive_of_ramificationIndex_square`. -/
theorem commonTop_rightNePrimitive_iff_leftNePrimitive_of_ramificationIndex_square
    [IsScalarTower baseK.valuationSubring base.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring
      commonTarget.valuationSubring]
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)] :
    Iff
      (ramificationIndex base.toDVF commonTarget.toDVF ≠
        ramificationIndex baseK.toDVF leftTarget.toDVF /
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF))
      (ramificationIndex leftTarget.toDVF commonTarget.toDVF ≠
        ramificationIndex baseK.toDVF base.toDVF /
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF)) := by
  have hiff :=
    commonTop_rightPrimitive_iff_leftPrimitive_of_ramificationIndex_square
      (baseK := baseK) (base := base) (leftTarget := leftTarget)
      (commonTarget := commonTarget)
      L K'
  constructor
  · intro hright_ne hleft
    exact hright_ne (hiff.mpr hleft)
  · intro hleft_ne hright
    exact hleft_ne (hiff.mp hright)

/-- If the lower left branch is totally tame, the right common-top degree
bound bounds the shared primitive quotient by the lower gcd. -/
theorem commonTop_exists_commonPrimitiveQuotient_le_gcd_of_leftCanonical_totalTame
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
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF) :
    ∃ commonQuotient,
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
        commonQuotient ≤
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF) := by
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
  exact exists_commonPrimitiveQuotient_le_gcd_of_mul_eq_mul_of_right_le
    hleft_pos hbase_pos (commonTop_ramificationIndex_square L K') hright_le

/-- Symmetric primitive-quotient bound from total tameness of the lower
base-change branch. -/
theorem commonTop_exists_commonPrimitiveQuotient_le_gcd_of_baseChangeCanonical_totalTame
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
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF) :
    ∃ commonQuotient,
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
        commonQuotient ≤
          Nat.gcd
            (ramificationIndex baseK.toDVF leftTarget.toDVF)
            (ramificationIndex baseK.toDVF base.toDVF) := by
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
  exact exists_commonPrimitiveQuotient_le_gcd_of_mul_eq_mul_of_left_le
    hleft_pos hbase_pos (commonTop_ramificationIndex_square L K') hleftTop_le

omit [baseK.valuation.HasExtension base.valuation]
  [leftTarget.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- If the lower left extension is totally tame and `L` and `K'` are linearly
disjoint, the right common-top ramification index divides the lower-left
ramification index. -/
theorem commonTop_right_ramificationIndex_dvd_left_of_totalTame_of_linearDisjoint
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hlin : L.LinearDisjoint K') :
    ramificationIndex base.toDVF commonTarget.toDVF ∣
      ramificationIndex baseK.toDVF leftTarget.toDVF := by
  have hdiv :
      ramificationIndex base.toDVF commonTarget.toDVF ∣ Module.finrank K L := by
    have hdegree :
        degree base.toDVF commonTarget.toDVF = Module.finrank K L := by
      change Module.finrank K' (L ⊔ K' : IntermediateField K Ω) =
        Module.finrank K L
      exact
        DiscreteValuationField.FieldCompositum.sup_finrank_over_right_eq_left_of_linearDisjoint
          L K' hlin
    have h :
        ramificationIndex base.toDVF commonTarget.toDVF ∣
          degree base.toDVF commonTarget.toDVF :=
      ramificationIndex_dvd_degree_of_finite_separable base commonTarget
    rw [hdegree] at h
    exact h
  rw [hleft.ramificationIndex_eq_degree]
  exact hdiv

omit [baseK.valuation.HasExtension leftTarget.valuation]
  [base.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Symmetric divisibility for a totally tame lower base-change branch. -/
theorem commonTop_left_ramificationIndex_dvd_baseChange_of_totalTame_of_linearDisjoint
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hlin : L.LinearDisjoint K') :
    ramificationIndex leftTarget.toDVF commonTarget.toDVF ∣
      ramificationIndex baseK.toDVF base.toDVF := by
  have hdiv :
      ramificationIndex leftTarget.toDVF commonTarget.toDVF ∣
        Module.finrank K K' := by
    have hdegree :
        degree leftTarget.toDVF commonTarget.toDVF = Module.finrank K K' := by
      change Module.finrank L (L ⊔ K' : IntermediateField K Ω) =
        Module.finrank K K'
      exact
        DiscreteValuationField.FieldCompositum.sup_finrank_over_left_eq_right_of_linearDisjoint
          L K' hlin
    have h :
        ramificationIndex leftTarget.toDVF commonTarget.toDVF ∣
          degree leftTarget.toDVF commonTarget.toDVF :=
      ramificationIndex_dvd_degree_of_finite_separable
        leftTarget commonTarget
    rw [hdegree] at h
    exact h
  rw [hbase.ramificationIndex_eq_degree]
  exact hdiv

omit [FiniteDimensional K L] [FiniteDimensional K K']
  [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] in
/-- Lower total tameness turns coprimality of ramification indices into linear
disjointness of the two field branches. -/
theorem linearDisjoint_of_lowerCanonical_totalTame_of_coprime
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime
      (ramificationIndex baseK.toDVF leftTarget.toDVF)
      (ramificationIndex baseK.toDVF base.toDVF)) :
    L.LinearDisjoint K' := by
  refine
    DiscreteValuationField.FieldCompositum.linearDisjoint_of_finrank_coprime
      L K' ?_
  have hcopDegree := hcop
  rw [hleft.ramificationIndex_eq_degree,
    hbase.ramificationIndex_eq_degree] at hcopDegree
  simpa using hcopDegree

omit [leftTarget.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Lower total tameness and lower coprimality supply the right common-top
branch divisibility. -/
theorem commonTop_right_ramificationIndex_dvd_left_of_lower_totalTame_of_coprime
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower base.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime
      (ramificationIndex baseK.toDVF leftTarget.toDVF)
      (ramificationIndex baseK.toDVF base.toDVF)) :
    ramificationIndex base.toDVF commonTarget.toDVF ∣
      ramificationIndex baseK.toDVF leftTarget.toDVF :=
  commonTop_right_ramificationIndex_dvd_left_of_totalTame_of_linearDisjoint
    L K' hleft
    (linearDisjoint_of_lowerCanonical_totalTame_of_coprime
      L K' hleft hbase hcop)

omit [base.valuation.HasExtension commonTarget.valuation]
  [baseK.valuation.HasExtension commonTarget.valuation] in
/-- Lower total tameness and lower coprimality supply the left common-top
branch divisibility. -/
theorem commonTop_left_ramificationIndex_dvd_baseChange_of_lower_totalTame_of_coprime
    [IsScalarTower baseK.valuationSubring base.valuationSubring K']
    [IsScalarTower baseK.valuationSubring leftTarget.valuationSubring L]
    [IsScalarTower leftTarget.valuationSubring commonTarget.valuationSubring
      (L ⊔ K' : IntermediateField K Ω)]
    (hleft : IsTotallyTamelyRamified baseK.toDVF leftTarget.toDVF)
    (hbase : IsTotallyTamelyRamified baseK.toDVF base.toDVF)
    (hcop : Nat.Coprime
      (ramificationIndex baseK.toDVF leftTarget.toDVF)
      (ramificationIndex baseK.toDVF base.toDVF)) :
    ramificationIndex leftTarget.toDVF commonTarget.toDVF ∣
      ramificationIndex baseK.toDVF base.toDVF :=
  commonTop_left_ramificationIndex_dvd_baseChange_of_totalTame_of_linearDisjoint
    L K' hbase
    (linearDisjoint_of_lowerCanonical_totalTame_of_coprime
      L K' hleft hbase hcop)

omit [baseK.valuation.HasExtension commonTarget.valuation] in
/-- The two upper ramification indices are coprime when the two lower indices
are coprime and the lower branches are totally tame. -/
theorem commonTop_canonical_ramificationIndex_coprime_of_lowerCanonical_totalTame_of_coprime
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
    Nat.Coprime
      (ramificationIndex base.toDVF commonTarget.toDVF)
      (ramificationIndex leftTarget.toDVF commonTarget.toDVF) := by
  have hright_dvd_left :
      ramificationIndex base.toDVF commonTarget.toDVF ∣
        ramificationIndex baseK.toDVF leftTarget.toDVF :=
    commonTop_right_ramificationIndex_dvd_left_of_lower_totalTame_of_coprime
      L K' hleft hbase hcop
  have hleftTop_dvd_base :
      ramificationIndex leftTarget.toDVF commonTarget.toDVF ∣
        ramificationIndex baseK.toDVF base.toDVF :=
    commonTop_left_ramificationIndex_dvd_baseChange_of_lower_totalTame_of_coprime
      L K' hleft hbase hcop
  exact (hcop.coprime_dvd_left hright_dvd_left).coprime_dvd_right
    hleftTop_dvd_base

/-- The common-top square, the two lower-branch divisibilities, and lower
coprimality reconstruct the lcm product for the right branch. -/
theorem commonTop_rightCanonical_lcmRamificationProduct_of_lowerCanonical_totalTame_of_coprime
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
    ramificationIndex baseK.toDVF base.toDVF *
        ramificationIndex base.toDVF commonTarget.toDVF =
      Nat.lcm
        (ramificationIndex baseK.toDVF leftTarget.toDVF)
        (ramificationIndex baseK.toDVF base.toDVF) := by
  have hright_dvd_left :
      ramificationIndex base.toDVF commonTarget.toDVF ∣
        ramificationIndex baseK.toDVF leftTarget.toDVF :=
    commonTop_right_ramificationIndex_dvd_left_of_lower_totalTame_of_coprime
      L K' hleft hbase hcop
  have hleftTop_dvd_base :
      ramificationIndex leftTarget.toDVF commonTarget.toDVF ∣
        ramificationIndex baseK.toDVF base.toDVF :=
    commonTop_left_ramificationIndex_dvd_baseChange_of_lower_totalTame_of_coprime
      L K' hleft hbase hcop
  have hbranchCop :
      Nat.Coprime
        (ramificationIndex base.toDVF commonTarget.toDVF)
        (ramificationIndex leftTarget.toDVF commonTarget.toDVF) :=
    commonTop_canonical_ramificationIndex_coprime_of_lowerCanonical_totalTame_of_coprime
      L K' hleft hbase hcop
  have hright_pos :
      0 < ramificationIndex base.toDVF commonTarget.toDVF := by
    let : Module.IsTorsionFree base.valuationSubring
        commonTarget.valuationSubring :=
      moduleIsTorsionFree_target_valuationSubring_of_finite_separable
        base commonTarget
    exact
      LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_pos
        base commonTarget
  have hleftTop_pos :
      0 < ramificationIndex leftTarget.toDVF commonTarget.toDVF := by
    let : Module.IsTorsionFree leftTarget.valuationSubring
        commonTarget.valuationSubring :=
      moduleIsTorsionFree_target_valuationSubring_of_finite_separable
        leftTarget commonTarget
    exact
      LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_pos
        leftTarget commonTarget
  exact TameAbhyankar.mul_eq_lcm_of_mul_eq_mul_of_dvd_of_dvd_of_coprime
    hright_pos hleftTop_pos (commonTop_ramificationIndex_square L K')
    hright_dvd_left hleftTop_dvd_base hbranchCop

end CommonTop

end FieldCompositum
end TameAbhyankar

end
