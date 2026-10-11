/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants
import Nyll.ValuedFieldTheory.Valuation.Henselian.Complete
import Nyll.ValuedFieldTheory.Valuation.Henselian.Core
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.AdicLimits
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Assembly
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Basic
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.CoefficientMinimum
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Complete
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.DegreeBounds
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.DivisionBounds
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.ErrorPowers
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.FiniteApproximation
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.InfiniteApproximation
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Iteration
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.PrincipalLimits
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Step
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Truncation
import Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.WeakLimits
import Nyll.ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialBounds
import Nyll.ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialLifting
import Nyll.ValuedFieldTheory.Valuation.Henselian.MonicFactorization
import Nyll.ValuedFieldTheory.Valuation.Henselian.NonmonicReduction
import Nyll.ValuedFieldTheory.Valuation.Henselian.PrimitiveFactorization
import Nyll.ValuedFieldTheory.Valuation.Henselian.PrimitiveReduction
import Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueAlgebraicExtensions
import Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionPrimitive
import Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionReduction
import Nyll.ValuedFieldTheory.Valuation.Henselian.ValuationExtensionCriterion
import Nyll.ValuedFieldTheory.Ramification.RamificationIndexComparison
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Basic
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Book.FiniteTameDegree
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValuedExtension.ResidueCharacteristic

/-!
# Tame predicates for finite separable valued extensions

For a finite separable extension of complete discretely valued fields, the
ambient valued extension is defectless.  Consequently tameness is controlled
directly by residue separability and the ramification index; no auxiliary
extension record or canonicalization constructor is needed.

The final section compares this canonical API with Neu1999's exponential-
valuation presentation when both presentations determine the same valuation
subrings.
-/

noncomputable section

universe u v w x

namespace ValuationTheory.DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]
variable [Algebra.IsSeparable K L]
variable [IsScalarTower base.valuationSubring target.valuationSubring L]

/-- In a finite separable extension, the ramification index divides the field
degree. -/
theorem ramificationIndex_dvd_degree_of_finite_separable :
    ramificationIndex base.toDVF target.toDVF ∣
      degree base.toDVF target.toDVF := by
  refine ⟨residueDegree base.toDVF target.toDVF, ?_⟩
  exact
    (open _root_.LocalFieldTheory.DiscreteValuationField.ValuedExtension in
      degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable
        base target)

/-- For a finite separable valued extension, tameness is exactly residue
separability together with the prime-to-residue-characteristic condition on
the ramification index. -/
theorem isTamelyRamified_iff_of_finite_separable :
    IsTamelyRamified base.toDVF target.toDVF ↔
      Algebra.IsSeparable base.residueField target.residueField ∧
        base.toDVF.PrimeToResidueCharacteristic
          (ramificationIndex base.toDVF target.toDVF) := by
  constructor
  · intro h
    exact ⟨h.residue_isSeparable, h.primeToResidueCharacteristic⟩
  · rintro ⟨hres, hprime⟩
    exact
      ⟨LocalFieldTheory.DiscreteValuationField.ValuedExtension.isDefectless_of_finite_separable
          base target,
        hres, hprime⟩

/-- Residue separability and the prime-to condition on the ramification index
imply tameness for a finite separable valued extension. -/
theorem isTamelyRamified_of_residue_isSeparable_of_primeTo_ramificationIndex
    (hres : Algebra.IsSeparable base.residueField target.residueField)
    (hprime :
      base.toDVF.PrimeToResidueCharacteristic
        (ramificationIndex base.toDVF target.toDVF)) :
    IsTamelyRamified base.toDVF target.toDVF :=
  (isTamelyRamified_iff_of_finite_separable base target).2 ⟨hres, hprime⟩

/-- A prime-to condition on the field degree implies the corresponding
condition on the ramification index and hence tameness. -/
theorem isTamelyRamified_of_residue_isSeparable_of_primeTo_degree
    (hres : Algebra.IsSeparable base.residueField target.residueField)
    (hprime :
      base.toDVF.PrimeToResidueCharacteristic
        (degree base.toDVF target.toDVF)) :
    IsTamelyRamified base.toDVF target.toDVF := by
  apply isTamelyRamified_of_residue_isSeparable_of_primeTo_ramificationIndex
    base target hres
  exact hprime.of_dvd
    (ramificationIndex_dvd_degree_of_finite_separable base target)

/-- An unramified finite separable valued extension with separable residue
extension is tame. -/
theorem isTamelyRamified_of_isUnramified_of_residue_isSeparable
    (hun : IsUnramified base.toDVF target.toDVF)
    (hres : Algebra.IsSeparable base.residueField target.residueField) :
    IsTamelyRamified base.toDVF target.toDVF :=
  ValuedExtension.isTamelyRamified_of_isUnramified_of_isDefectless_of_residue_isSeparable
    base.toDVF target.toDVF hun
    (LocalFieldTheory.DiscreteValuationField.ValuedExtension.isDefectless_of_finite_separable
      base target)
    hres

/-- Total tame ramification of a finite separable valued extension is residue
separability, the prime-to condition on the ramification index, and residue
degree one. -/
theorem isTotallyTamelyRamified_iff_of_finite_separable :
    IsTotallyTamelyRamified base.toDVF target.toDVF ↔
      Algebra.IsSeparable base.residueField target.residueField ∧
        base.toDVF.PrimeToResidueCharacteristic
          (ramificationIndex base.toDVF target.toDVF) ∧
        residueDegree base.toDVF target.toDVF = 1 := by
  constructor
  · intro h
    exact
      ⟨h.isTamelyRamified.residue_isSeparable,
        h.isTamelyRamified.primeToResidueCharacteristic,
        h.isTotallyRamified⟩
  · rintro ⟨hres, hprime, hf⟩
    exact
      ⟨(isTamelyRamified_iff_of_finite_separable base target).2
          ⟨hres, hprime⟩,
        hf⟩

/-- Degree form of the total-tameness criterion. -/
theorem isTotallyTamelyRamified_iff_primeTo_degree_of_finite_separable :
    IsTotallyTamelyRamified base.toDVF target.toDVF ↔
      Algebra.IsSeparable base.residueField target.residueField ∧
        base.toDVF.PrimeToResidueCharacteristic
          (degree base.toDVF target.toDVF) ∧
        residueDegree base.toDVF target.toDVF = 1 := by
  constructor
  · intro h
    exact
      ⟨h.isTamelyRamified.residue_isSeparable,
        h.primeToResidueCharacteristic_degree,
        h.isTotallyRamified⟩
  · rintro ⟨hres, hprime, hf⟩
    apply (isTotallyTamelyRamified_iff_of_finite_separable base target).2
    refine ⟨hres, ?_, hf⟩
    have hram :
        ramificationIndex base.toDVF target.toDVF =
          degree base.toDVF target.toDVF :=
      (open _root_.LocalFieldTheory.DiscreteValuationField.ValuedExtension in
        residueDegree_eq_one_iff_ramificationIndex_eq_degree_of_finite_separable base target).1 hf
    simpa [hram] using hprime

/-- Introduction form of the direct total-tameness criterion. -/
theorem
 isTotallyTamelyRamified_of_residue_isSeparable_of_primeTo_ramificationIndex_of_residueDegree_eq_one
    (hres : Algebra.IsSeparable base.residueField target.residueField)
    (hprime :
      base.toDVF.PrimeToResidueCharacteristic
        (ramificationIndex base.toDVF target.toDVF))
    (hf : residueDegree base.toDVF target.toDVF = 1) :
    IsTotallyTamelyRamified base.toDVF target.toDVF :=
  (isTotallyTamelyRamified_iff_of_finite_separable base target).2
    ⟨hres, hprime, hf⟩

/-- Introduction form of the degree-based total-tameness criterion. -/
theorem isTotallyTamelyRamified_of_residue_isSeparable_of_primeTo_degree_of_residueDegree_eq_one
    (hres : Algebra.IsSeparable base.residueField target.residueField)
    (hprime :
      base.toDVF.PrimeToResidueCharacteristic
        (degree base.toDVF target.toDVF))
    (hf : residueDegree base.toDVF target.toDVF = 1) :
    IsTotallyTamelyRamified base.toDVF target.toDVF :=
  (isTotallyTamelyRamified_iff_primeTo_degree_of_finite_separable base target).2
    ⟨hres, hprime, hf⟩

end ValuedExtension
end ValuationTheory.DiscreteValuationField

namespace TameAbhyankar

open AlgebraicNumberTheory.Valuations

private theorem residue_isSeparable_of_bookFiniteTame
    {K : Type u} {L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {base : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K}
    {target : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, x} L}
    [base.valuation.HasExtension target.valuation]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, vL (algebraMap K L a) = vK a)
    (hTame : FiniteTamelyRamifiedExtension vK vL hExt)
    (hV : LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK =
      base.valuation.valuationSubring)
    (hW : LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vL =
      target.valuation.valuationSubring) :
    Algebra.IsSeparable base.residueField target.residueField := by
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let B := base.valuationSubring
  let T := target.valuationSubring
  let iBook := unramifiedValuationRingValuationRingMap vK vL hExt
  let iCan : B →+* T := algebraMap B T
  let : IsLocalHom iBook :=
    unramifiedValuationRingValuationRingMap_isLocalHom vK vL hExt
  let : IsLocalHom iCan := by
    dsimp only [iCan]
    infer_instance
  let : Algebra (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) :=
    (IsLocalRing.ResidueField.map iBook).toAlgebra
  let eV : V ≃+* B := RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring hV)
  let eW : W ≃+* T := RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring hW)
  let rV := IsLocalRing.ResidueField.mapEquiv eV
  let rW := IsLocalRing.ResidueField.mapEquiv eW
  have hcomm :
      rW.toRingHom.comp (IsLocalRing.ResidueField.map iBook) =
        (algebraMap (IsLocalRing.ResidueField B)
          (IsLocalRing.ResidueField T)).comp rV.toRingHom := by
    rw [ValuationTheory.DiscreteValuationField.ResidueField.algebraMap_eq_map_algebraMap]
    ext qx
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective qx
    simp only [RingHom.comp_apply, rV, rW,
      IsLocalRing.ResidueField.map_residue]
    apply congrArg (IsLocalRing.residue T)
    apply Subtype.ext
    rfl
  let : Algebra.IsSeparable (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) := hTame.2.1
  exact Algebra.IsSeparable.of_equiv_equiv rV rW hcomm.symm

/--
A finite tame extension in the exponential-valuation (book) presentation is
tame for the complete-DVF valued extension, provided the book and
CompleteDVF valuation rings are the same.

The proof transports the two residue fields through residue-field ring
equivalences, compares the local ramification indices through the induced
ring equivalences, and transports the residue characteristic by `ringChar`.
-/
theorem isTamelyRamified_of_bookFiniteTame
    {K : Type u} {L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {base : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K}
    {target : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, x} L}
    [base.valuation.HasExtension target.valuation]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, vL (algebraMap K L a) = vK a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    (hTame : FiniteTamelyRamifiedExtension vK vL hExt)
    (hV : LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK =
      base.valuation.valuationSubring)
    (hW : LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vL =
      target.valuation.valuationSubring) :
    ValuationTheory.DiscreteValuationField.ValuedExtension.IsTamelyRamified
      base.toDVF target.toDVF := by
  have hVSub : LubinTate.Valuations.exponentialValuationSubring vK =
      base.valuation.valuationSubring.toSubring :=
    congrArg ValuationSubring.toSubring hV
  have hWSub : LubinTate.Valuations.exponentialValuationSubring vL =
      target.valuation.valuationSubring.toSubring :=
    congrArg ValuationSubring.toSubring hW
  have hram : exponentialRamificationIndex vK vL =
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF :=
    RamificationTheory.exponentialRamificationIndex_eq_ramificationIndex_of_valuationSubrings_eq
      vK vL hExt hV hW
  have hres : Algebra.IsSeparable base.residueField target.residueField :=
    residue_isSeparable_of_bookFiniteTame vK vL hExt hTame hV hW
  have hchar : residueCharacteristic vK =
      base.toDVF.residueCharacteristic := by
    let V := LubinTate.Valuations.exponentialValuationSubring vK
    let B := base.valuationSubring
    let eV : V ≃+* B := RingEquiv.subringCongr hVSub
    let rV := IsLocalRing.ResidueField.mapEquiv eV
    let : Algebra (IsLocalRing.ResidueField V)
        (IsLocalRing.ResidueField B) := rV.toRingHom.toAlgebra
    change ringChar (IsLocalRing.ResidueField V) =
      ringChar (IsLocalRing.ResidueField B)
    exact Algebra.ringChar_eq _ _
  have hdegree :=
    finiteTamelyRamifiedExtension_finrank_maximalUnramified_eq_ramificationIndex
      vK vL hExt hhens hTame
  have hcoprime : Nat.Coprime (exponentialRamificationIndex vK vL)
      (residueCharacteristic vK) := by
    rw [← hdegree]
    exact hTame.2.2
  rw [hram, hchar] at hcoprime
  have hprime : base.toDVF.PrimeToResidueCharacteristic
      (ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF) :=
    Or.inr hcoprime
  exact
    (open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension in
      isTamelyRamified_of_residue_isSeparable_of_primeTo_ramificationIndex
        base target hres hprime)

end TameAbhyankar

end
