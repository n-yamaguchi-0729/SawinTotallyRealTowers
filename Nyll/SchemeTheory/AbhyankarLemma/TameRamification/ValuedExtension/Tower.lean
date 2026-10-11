/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValuedExtension.ResidueCharacteristic

/-!
# Tame ramification in valued towers

Tameness and total tameness propagate through a finite valued tower.  The
statements use the canonical invariants of `ValuedExtension` directly, so the
same declarations apply to complete and Henselian discretely valued fields
through their `toDVF` projections.
-/

noncomputable section

universe u v w x y z a b

namespace ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {M : Type y} {L : Type w}
variable [Field K] [Field M] [Field L]
variable [Algebra K M] [Algebra M L] [Algebra K L]
variable [IsScalarTower K M L]
variable [FiniteDimensional K M] [FiniteDimensional M L]
variable [FiniteDimensional K L]
variable {base : DVF.{u, v} K}
variable {middle : DVF.{y, z} M}
variable {target : DVF.{w, x} L}
variable [base.valuation.HasExtension middle.valuation]
variable [middle.valuation.HasExtension target.valuation]
variable [base.valuation.HasExtension target.valuation]

omit [FiniteDimensional K M] [FiniteDimensional M L]
  [FiniteDimensional K L] in
/-- The residue-field algebra maps induced by a valued tower form a scalar
tower. -/
theorem residueField_isScalarTower :
    IsScalarTower base.residueField middle.residueField target.residueField := by
  have hcomp (x : base.residueField) :
      residueMap middle target (residueMap base middle x) =
        residueMap base target x := by
    obtain ⟨a, rfl⟩ := base.residue_surjective x
    rw [residueMap_residue base middle a,
      residueMap_residue middle target (integerMap base middle a),
      residueMap_residue base target a]
    congr 1
    ext
    simpa only [integerMap_apply] using
      (IsScalarTower.algebraMap_apply K M L (a : K)).symm
  apply IsScalarTower.of_algebraMap_eq
  intro x
  simpa [residueMap] using (hcomp x).symm

omit [FiniteDimensional K M] [FiniteDimensional M L]
  [FiniteDimensional K L] in
/-- Surjectivity of the two residue maps implies surjectivity of the composite
residue map. -/
theorem residueMap_surjective_tower
    (hbase : Function.Surjective (residueMap base middle))
    (htarget : Function.Surjective (residueMap middle target)) :
    Function.Surjective (residueMap base target) := by
  intro z
  obtain ⟨y, rfl⟩ := htarget z
  obtain ⟨x, rfl⟩ := hbase y
  refine ⟨x, ?_⟩
  let : IsScalarTower base.residueField middle.residueField
      target.residueField :=
    residueField_isScalarTower (base := base) (middle := middle)
      (target := target)
  simpa [residueMap] using
    (IsScalarTower.algebraMap_apply base.residueField middle.residueField
      target.residueField x)

omit [IsScalarTower K M L] [FiniteDimensional K M]
  [FiniteDimensional M L] [FiniteDimensional K L] in
/-- Multiplicativity of the canonical ramification index in a valued tower. -/
theorem ramificationIndex_tower
    [IsScalarTower base.valuationSubring middle.valuationSubring
      target.valuationSubring] :
    ramificationIndex base target =
      ramificationIndex base middle * ramificationIndex middle target := by
  simpa [ramificationIndex, integerMap] using
    (Ideal.ramificationIdx'_algebra_tower
      (maximalIdeal_map_integerMap_ne_bot middle target)
      (maximalIdeal_map_integerMap_ne_bot base target)
      (maximalIdeal_map_integerMap_le middle target))

omit [IsScalarTower K M L] [FiniteDimensional K M]
  [FiniteDimensional M L] [FiniteDimensional K L] in
/-- Multiplicativity of the canonical residue degree in a valued tower. -/
theorem residueDegree_tower
    [IsScalarTower base.valuationSubring middle.valuationSubring
      target.valuationSubring] :
    residueDegree base target =
      residueDegree base middle * residueDegree middle target := by
  let : target.maximalIdeal.LiesOver middle.maximalIdeal :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_liesOver_of_hasExtension
      middle.valuation target.valuation
  simpa only [residueDegree] using
    (Ideal.inertiaDeg_tower (R := base.valuationSubring)
      middle.maximalIdeal target.maximalIdeal)

omit [FiniteDimensional K L]
  [base.valuation.HasExtension middle.valuation]
  [middle.valuation.HasExtension target.valuation]
  [base.valuation.HasExtension target.valuation] in
/-- Multiplicativity of field degrees in a finite valued tower. -/
theorem degree_tower :
    degree base target = degree base middle * degree middle target := by
  simpa [degree] using (Module.finrank_mul_finrank K M L).symm

omit [IsScalarTower K M L] [FiniteDimensional K M]
  [FiniteDimensional M L] [FiniteDimensional K L] in
/-- A composite valued extension is totally ramified exactly when both steps
are totally ramified. -/
theorem isTotallyRamified_tower_iff
    [IsScalarTower base.valuationSubring middle.valuationSubring
      target.valuationSubring] :
    IsTotallyRamified base target ↔
      IsTotallyRamified base middle ∧ IsTotallyRamified middle target := by
  change residueDegree base target = 1 ↔
    residueDegree base middle = 1 ∧ residueDegree middle target = 1
  rw [residueDegree_tower (base := base) (middle := middle)
    (target := target)]
  constructor
  · intro h
    exact ⟨Nat.eq_one_of_mul_eq_one_right h,
      Nat.eq_one_of_mul_eq_one_left h⟩
  · rintro ⟨hbase, htarget⟩
    rw [hbase, htarget, one_mul]

omit [FiniteDimensional K L] in
/-- Defectlessness is preserved by a finite valued tower. -/
theorem isDefectless_tower
    [IsScalarTower base.valuationSubring middle.valuationSubring
      target.valuationSubring]
    (hbase : IsDefectless base middle)
    (htarget : IsDefectless middle target) :
    IsDefectless base target := by
  have hbase' :
      degree base middle =
        ramificationIndex base middle * residueDegree base middle :=
    hbase
  have htarget' :
      degree middle target =
        ramificationIndex middle target * residueDegree middle target :=
    htarget
  change degree base target =
    ramificationIndex base target * residueDegree base target
  rw [degree_tower (base := base) (middle := middle) (target := target),
    ramificationIndex_tower (base := base) (middle := middle)
      (target := target),
    residueDegree_tower (base := base) (middle := middle)
      (target := target),
    hbase', htarget']
  ac_rfl

omit [FiniteDimensional K L] in
/-- Tame ramification is preserved by a finite valued tower. -/
theorem isTamelyRamified_tower
    [IsScalarTower base.valuationSubring middle.valuationSubring
      target.valuationSubring]
    (hbase : IsTamelyRamified base middle)
    (htarget : IsTamelyRamified middle target) :
    IsTamelyRamified base target := by
  refine ⟨isDefectless_tower hbase.isDefectless htarget.isDefectless, ?_, ?_⟩
  · let : IsScalarTower base.residueField middle.residueField
        target.residueField :=
      residueField_isScalarTower (base := base) (middle := middle)
        (target := target)
    let : Algebra.IsSeparable base.residueField middle.residueField :=
      hbase.residue_isSeparable
    let : Algebra.IsSeparable middle.residueField target.residueField :=
      htarget.residue_isSeparable
    exact Algebra.IsSeparable.trans
      base.residueField middle.residueField target.residueField
  · rw [ramificationIndex_tower (base := base) (middle := middle)
      (target := target)]
    exact hbase.primeToResidueCharacteristic.mul
      (DVF.primeToResidueCharacteristic_of_target
        (base := base) (target := middle)
        htarget.primeToResidueCharacteristic)

omit [FiniteDimensional K L] in
/-- Total tame ramification is preserved by a finite valued tower. -/
theorem isTotallyTamelyRamified_tower
    [IsScalarTower base.valuationSubring middle.valuationSubring
      target.valuationSubring]
    (hbase : IsTotallyTamelyRamified base middle)
    (htarget : IsTotallyTamelyRamified middle target) :
    IsTotallyTamelyRamified base target :=
  ⟨isTamelyRamified_tower hbase.isTamelyRamified
      htarget.isTamelyRamified,
    (isTotallyRamified_tower_iff (base := base) (middle := middle)
      (target := target)).2
      ⟨hbase.isTotallyRamified, htarget.isTotallyRamified⟩⟩

section Square

variable {M' : Type a} [Field M']
variable [Algebra K M'] [Algebra M' L]
variable [IsScalarTower K M' L]
variable [FiniteDimensional K M'] [FiniteDimensional M' L]
variable {leftMiddle : DVF.{a, b} M'}
variable [base.valuation.HasExtension leftMiddle.valuation]
variable [leftMiddle.valuation.HasExtension target.valuation]

omit [IsScalarTower K M L] [IsScalarTower K M' L]
  [FiniteDimensional K M] [FiniteDimensional M L]
  [FiniteDimensional K L] [FiniteDimensional K M']
  [FiniteDimensional M' L] in
/-- The two products of ramification indices around a valued square agree. -/
theorem ramificationIndex_square
    [IsScalarTower base.valuationSubring middle.valuationSubring
      target.valuationSubring]
    [IsScalarTower base.valuationSubring leftMiddle.valuationSubring
      target.valuationSubring] :
    ramificationIndex base middle * ramificationIndex middle target =
      ramificationIndex base leftMiddle * ramificationIndex leftMiddle target := by
  calc
    ramificationIndex base middle * ramificationIndex middle target =
        ramificationIndex base target :=
      (ramificationIndex_tower (base := base) (middle := middle)
        (target := target)).symm
    _ = ramificationIndex base leftMiddle * ramificationIndex leftMiddle target :=
      ramificationIndex_tower (base := base) (middle := leftMiddle)
        (target := target)

end Square

end ValuationTheory.DiscreteValuationField.ValuedExtension

end
