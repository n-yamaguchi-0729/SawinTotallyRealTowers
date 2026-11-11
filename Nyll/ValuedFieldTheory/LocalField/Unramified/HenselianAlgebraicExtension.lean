/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.Unramified.Definitions
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.AbsoluteValues
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.ExponentialValuations
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import Nyll.ValuedFieldTheory.Valuation.Henselian.Core
public import Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionHenselian
public import Nyll.ValuedFieldTheory.Valuation.Henselian.SimpleRootFactorization
public import Nyll.ValuedFieldTheory.Valuation.Henselian.MonicFactorization

/-!
# Henselianity along algebraic valued extensions

The proof of the unramified base-change theorem applies Hensel's lemma after
base change from `K` to an algebraic extension `K'`.  This file supplies the
source used there: an algebraic extension of a Henselian valuation is again
Henselian. The Henselian ring criterion applies to the original valuation
rings in independent field universes and supplies the full factorization
property on the target ring.
-/

@[expose] public section

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

universe u v


/-- The exponential presentation of a Henselian valuation has a unique
valuation-subring extension to every algebraic field in the same universe.
This is the unique-extension criterion transported through the associated nonarchimedean
absolute value. -/
theorem exponentialValuation_hasUniqueAlgebraicValuationSubringExtensions
    {K : Type u} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    HasUniqueAlgebraicValuationSubringExtensions
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v) := by
  let av := exponentialAssociatedAbsoluteValue v
  have hav : LubinTate.Valuations.AssociatedAbsoluteValue v (Real.exp 1) av :=
    exponentialAssociatedAbsoluteValue_associated v
  have havNonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue av :=
    associatedAbsoluteValue_nonarchimedean v (Real.exp 1) av hav
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let Va := absoluteValueValuationSubring av havNonarch
  have hV : Vv = Va :=
    associatedAbsoluteValue_valuationSubring_eq
      v (Real.exp 1) av havNonarch hav
  have hhensA : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
    Va.valuation := by
    rw [← hV]
    exact hhens
  change HasUniqueAlgebraicValuationSubringExtensions Vv
  rw [hV]
  exact henselianUniqueExtension_unique_algebraic_valuationSubring_extensions_of_henselian
    av havNonarch hhensA


/-- An algebraic extension of a Henselian valued field is Henselian for its
unique extended valuation.

Only the actual exact extension of the two exponential valuations is an
input. The original factorization property supplies a Henselian ring;
Henselianity then extends to the same target valuation ring, even when the
two fields lie in different universes. The final factorization property uses
that same ring and the original exact valuation extension. -/
theorem henselianValuation_of_algebraic_extension
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w).valuation := by
  let av := exponentialAssociatedAbsoluteValue v
  let aw := exponentialAssociatedAbsoluteValue w
  have hav : LubinTate.Valuations.AssociatedAbsoluteValue v (Real.exp 1) av :=
    exponentialAssociatedAbsoluteValue_associated v
  have haw : LubinTate.Valuations.AssociatedAbsoluteValue w (Real.exp 1) aw :=
    exponentialAssociatedAbsoluteValue_associated w
  have havNonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue av :=
    associatedAbsoluteValue_nonarchimedean v (Real.exp 1) av hav
  have hawNonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue aw :=
    associatedAbsoluteValue_nonarchimedean w (Real.exp 1) aw haw
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
  let Va := absoluteValueValuationSubring av havNonarch
  let Wa := absoluteValueValuationSubring aw hawNonarch
  have hV : Vv = Va :=
    associatedAbsoluteValue_valuationSubring_eq
      v (Real.exp 1) av havNonarch hav
  have hW : Wv = Wa :=
    associatedAbsoluteValue_valuationSubring_eq
      w (Real.exp 1) aw hawNonarch haw
  have habsExt : ∀ a : K, aw (algebraMap K L a) = av a :=
    associatedAbsoluteValue_extends
      v w hExt (Real.exp 1) av aw hav haw
  have hVaWa : Va.valuation.HasExtension Wa.valuation :=
    absoluteValueValuation_hasExtension_of_extends
      av aw havNonarch hawNonarch habsExt
  have hVvWv : Vv.valuation.HasExtension Wv.valuation := by
    rw [hV, hW]
    exact hVaWa
  let : Vv.valuation.HasExtension Wv.valuation := hVvWv
  have hfactor : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty Vv := by
    change ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      Vv.valuation.valuationSubring at hhens
    rw [ValuationSubring.valuationSubring_valuation] at hhens
    exact @hhens
  let : HenselianRing Vv (IsLocalRing.maximalIdeal Vv) :=
    _root_.DiscreteValuationField.henselianRing_of_monicResidualCoprimeFactorLifting
      (_root_.DiscreteValuationField.monicResidualCoprimeFactorLifting_of_henselFactorization
        hfactor)
  let : HenselianRing Wv (IsLocalRing.maximalIdeal Wv) :=
    ValuationTheory.Henselian.henselianRing_of_algebraic_extension Vv Wv
  change ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
    Wv.valuation.valuationSubring
  rw [ValuationSubring.valuationSubring_valuation]
  exact _root_.DiscreteValuationField.henselFactorization_of_henselianRing Wv

end Valuations
end AlgebraicNumberTheory

end
