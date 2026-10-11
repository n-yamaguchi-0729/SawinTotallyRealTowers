/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core

/-!
# Tame ramification predicates

This file defines tame ramification directly for the ambient valued extension
`base / target`.  No proof-irrelevant extension record is introduced: complete
and Henselian discretely valued fields use the same definitions through their
canonical `toDVF` projections.
-/

noncomputable section

universe u v w x

namespace ValuationTheory.DiscreteValuationField

namespace DVF

variable {K : Type u} [Field K]

/-- The residue characteristic of a discretely valued field, expressed as `0`
in characteristic zero and as the positive prime characteristic otherwise. -/
def residueCharacteristic (F : DVF.{u, v} K) : ℕ :=
  ringChar F.residueField

@[simp] theorem residueCharacteristic_eq_ringChar (F : DVF.{u, v} K) :
    F.residueCharacteristic = ringChar F.residueField :=
  rfl

/-- A natural number is prime to the residue characteristic.  In residue
characteristic zero this condition is vacuous. -/
def PrimeToResidueCharacteristic (F : DVF.{u, v} K) (n : ℕ) : Prop :=
  F.residueCharacteristic = 0 ∨ Nat.Coprime n F.residueCharacteristic

theorem primeToResidueCharacteristic_of_residueCharacteristic_eq_zero
    (F : DVF.{u, v} K) {n : ℕ}
    (hchar : F.residueCharacteristic = 0) :
    F.PrimeToResidueCharacteristic n :=
  Or.inl hchar

theorem primeToResidueCharacteristic_iff_of_residueCharacteristic_ne_zero
    (F : DVF.{u, v} K) {n : ℕ}
    (hchar : F.residueCharacteristic ≠ 0) :
    F.PrimeToResidueCharacteristic n ↔
      Nat.Coprime n F.residueCharacteristic := by
  constructor
  · intro h
    exact h.resolve_left hchar
  · exact Or.inr

theorem residueCharacteristic_coprime_of_primeToResidueCharacteristic
    (F : DVF.{u, v} K) {n : ℕ}
    (hchar : F.residueCharacteristic ≠ 0)
    (hn : F.PrimeToResidueCharacteristic n) :
    Nat.Coprime n F.residueCharacteristic :=
  (F.primeToResidueCharacteristic_iff_of_residueCharacteristic_ne_zero hchar).1 hn

theorem primeToResidueCharacteristic_one (F : DVF.{u, v} K) :
    F.PrimeToResidueCharacteristic 1 := by
  by_cases hchar : F.residueCharacteristic = 0
  · exact Or.inl hchar
  · exact Or.inr (Nat.coprime_one_left F.residueCharacteristic)

end DVF

namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : DVF.{u, v} K) (target : DVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- A finite valued extension is tamely ramified when it is defectless, its
residue-field extension is separable, and its ramification index is prime to
the residue characteristic. -/
def IsTamelyRamified : Prop :=
  IsDefectless base target ∧
    Algebra.IsSeparable base.residueField target.residueField ∧
      base.PrimeToResidueCharacteristic (ramificationIndex base target)

theorem isTamelyRamified_def :
    IsTamelyRamified base target ↔
      IsDefectless base target ∧
        Algebra.IsSeparable base.residueField target.residueField ∧
          base.PrimeToResidueCharacteristic (ramificationIndex base target) :=
  Iff.rfl

theorem IsTamelyRamified.isDefectless
    (hE : IsTamelyRamified base target) :
    IsDefectless base target :=
  hE.1

theorem IsTamelyRamified.residue_isSeparable
    (hE : IsTamelyRamified base target) :
    Algebra.IsSeparable base.residueField target.residueField :=
  hE.2.1

theorem IsTamelyRamified.primeToResidueCharacteristic
    (hE : IsTamelyRamified base target) :
    base.PrimeToResidueCharacteristic (ramificationIndex base target) :=
  hE.2.2

theorem IsTamelyRamified.ramificationIndex_coprime_residueCharacteristic
    (hE : IsTamelyRamified base target)
    (hchar : base.residueCharacteristic ≠ 0) :
    Nat.Coprime (ramificationIndex base target) base.residueCharacteristic :=
  base.residueCharacteristic_coprime_of_primeToResidueCharacteristic hchar
    hE.primeToResidueCharacteristic

theorem isTamelyRamified_of_isUnramified_of_isDefectless_of_residue_isSeparable
    (hun : IsUnramified base target)
    (hdef : IsDefectless base target)
    (hres : Algebra.IsSeparable base.residueField target.residueField) :
    IsTamelyRamified base target := by
  refine ⟨hdef, hres, ?_⟩
  rw [hun]
  exact base.primeToResidueCharacteristic_one

theorem IsTamelyRamified.degree_eq_ramificationIndex_mul_residueDegree
    (hE : IsTamelyRamified base target) :
    degree base target = ramificationIndex base target * residueDegree base target :=
  hE.isDefectless

/-- Totally tamely ramified means tame and residue degree one. -/
def IsTotallyTamelyRamified : Prop :=
  IsTamelyRamified base target ∧ IsTotallyRamified base target

theorem isTotallyTamelyRamified_def :
    IsTotallyTamelyRamified base target ↔
      IsTamelyRamified base target ∧ IsTotallyRamified base target :=
  Iff.rfl

theorem IsTotallyTamelyRamified.isTamelyRamified
    (hE : IsTotallyTamelyRamified base target) :
    IsTamelyRamified base target :=
  hE.1

theorem IsTotallyTamelyRamified.isTotallyRamified
    (hE : IsTotallyTamelyRamified base target) :
    IsTotallyRamified base target :=
  hE.2

theorem IsTotallyTamelyRamified.ramificationIndex_eq_degree
    (hE : IsTotallyTamelyRamified base target) :
    ramificationIndex base target = degree base target := by
  rw [hE.isTamelyRamified.degree_eq_ramificationIndex_mul_residueDegree,
    hE.isTotallyRamified, mul_one]

theorem IsTotallyTamelyRamified.primeToResidueCharacteristic_degree
    (hE : IsTotallyTamelyRamified base target) :
    base.PrimeToResidueCharacteristic (degree base target) := by
  have hdeg : ramificationIndex base target = degree base target :=
    hE.ramificationIndex_eq_degree
  simpa [hdeg] using hE.isTamelyRamified.primeToResidueCharacteristic

end ValuedExtension

end ValuationTheory.DiscreteValuationField

end
