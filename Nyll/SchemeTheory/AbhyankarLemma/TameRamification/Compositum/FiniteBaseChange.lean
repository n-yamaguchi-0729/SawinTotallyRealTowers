/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

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
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Compositum
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValuedExtension.Canonical
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Book.IndexAbsorption
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Book.BaseChange

/-!
# Finite tame base change on the actual compositum

This is the finite tame-base-change corollary used on the way to Abhyankar's
lemma.  Starting only with compatibility of the book and CompleteDVF
presentations at the original base, it constructs the valuation on the actual
compositum `L ⊔ K'`, uses finite-separable uniqueness to identify the two
upper valuation rings, applies Neu1999 Corollary 7.8, and returns tame
ramification in the canonical CompleteDVF API.
-/

noncomputable section

universe u v w x

namespace TameAbhyankar

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open DiscreteValuationField.FieldCompositum
open AlgebraicNumberTheory.Valuations

/-- Exact extension of exponential valuations induces extension of the
canonical valuations attached to their valuation subrings. -/
theorem bookValuationSubring_hasExtension_of_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    let V := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
    V.valuation.HasExtension W.valuation := by
  let V := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
  apply _root_.Valuation.HasExtension.ofComapInteger
  rw [ValuationSubring.integer_valuation, ValuationSubring.integer_valuation]
  ext a
  change (0 : WithTop ℝ) ≤ w (algebraMap K L a) ↔
    (0 : WithTop ℝ) ≤ v a
  rw [hExt]

/-- If a CompleteDVF uses the source book valuation ring, exact extension of
book valuations gives an extension of its bundled valuation. -/
theorem completeDVF_hasExtension_bookValuationSubring_of_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (base : CompleteDVF K)
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hBase : LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v =
      base.valuation.valuationSubring) :
    base.valuation.HasExtension
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w).valuation := by
  let V := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
  have hVW : V.valuation.HasExtension W.valuation :=
    bookValuationSubring_hasExtension_of_extends v w hExt
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext a
  simp only [Subring.mem_comap, _root_.Valuation.mem_integer_iff]
  let : V.valuation.HasExtension W.valuation := hVW
  rw [_root_.Valuation.HasExtension.val_map_le_one_iff
    (vR := V.valuation) (vA := W.valuation) a]
  rw [ValuationSubring.valuation_le_one_iff,
    ← base.valuation.mem_valuationSubring_iff]
  exact SetLike.ext_iff.mp hBase a

/--
Construct the actual common top and compare its two book valuation rings with
the canonical CompleteDVF valuation rings.  Only the comparison at `K` is an
input; the comparisons at `K'` and `L ⊔ K'` follow from uniqueness of a
finite-separable extension of a complete valuation.
-/
theorem exists_actualCommonTop_bookFiniteTame_and_compatible
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω]
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K']
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K K']
    {baseK : CompleteDVF.{u, v} K}
    {rightBase : CompleteDVF.{u, w} K'}
    [baseK.valuation.HasExtension rightBase.valuation]
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (wΩ : LubinTate.Valuations.ExponentialValuation Ω)
    (hKΩ : ∀ a : K, wΩ (algebraMap K Ω a) = vK a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    (hTame : FiniteTamelyRamifiedExtension vK
      (exponentialValuationRestrict wΩ L)
      (exponentialValuationRestrict_extends vK wΩ hKΩ L))
    (hBaseBook :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK =
        baseK.valuation.valuationSubring) :
    let Top := (L ⊔ K' : IntermediateField K Ω)
    ∃ commonTarget : CompleteDVF.{u, 0} Top,
      ∃ hRight : rightBase.valuation.HasExtension commonTarget.valuation,
        letI : rightBase.valuation.HasExtension commonTarget.valuation := hRight
        let wRight := exponentialValuationRestrict wΩ K'
        let wTop := exponentialValuationRestrict wΩ Top
        let hRightTop : ∀ a : K',
            wTop (algebraMap K' Top a) = wRight a := by intro a; rfl
        letI : FiniteDimensional K' Top :=
          finiteDimensional_sup_over_right L K'
        FiniteTamelyRamifiedExtension wRight wTop hRightTop ∧
          LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wRight =
            rightBase.valuation.valuationSubring ∧
          LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wTop =
            commonTarget.valuation.valuationSubring := by
  let Top := (L ⊔ K' : IntermediateField K Ω)
  let wRight := exponentialValuationRestrict wΩ K'
  let wTop := exponentialValuationRestrict wΩ Top
  let hBaseRight :=
    exponentialValuationRestrict_extends vK wΩ hKΩ K'
  let hRightTop : ∀ a : K',
      wTop (algebraMap K' Top a) = wRight a := by
    intro a
    rfl
  let : FiniteDimensional K' Top :=
    finiteDimensional_sup_over_right L K'
  let : Algebra.IsSeparable K' Top :=
    isSeparable_sup_over_right_of_left L K'
  obtain ⟨commonTarget, hRight, _hIntegral, _hFundamental⟩ :=
    ValuedExtension.exists_integralClosure_standard_fundamental_identity
      (K := K') (L := Top) rightBase
  let : rightBase.valuation.HasExtension commonTarget.valuation := hRight
  have hBookRightExt : baseK.valuation.HasExtension
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wRight).valuation :=
    completeDVF_hasExtension_bookValuationSubring_of_eq
      baseK vK wRight hBaseRight hBaseBook
  let : baseK.valuation.HasExtension
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wRight).valuation :=
    hBookRightExt
  have hRightBook :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wRight =
        rightBase.valuation.valuationSubring := by
    simpa only [ValuationSubring.valuationSubring_valuation] using
      valuationSubring_eq_target_of_finite_separable baseK rightBase
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wRight).valuation
  have hBookTopExt : rightBase.valuation.HasExtension
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wTop).valuation :=
    completeDVF_hasExtension_bookValuationSubring_of_eq
      rightBase wRight wTop hRightTop hRightBook
  let : rightBase.valuation.HasExtension
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wTop).valuation :=
    hBookTopExt
  have hTopBook :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wTop =
        commonTarget.valuation.valuationSubring := by
    simpa only [ValuationSubring.valuationSubring_valuation] using
      valuationSubring_eq_target_of_finite_separable rightBase commonTarget
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wTop).valuation
  have hTopTame :
      FiniteTamelyRamifiedExtension wRight wTop hRightTop :=
    finiteTamelyRamifiedExtension_commonTop_of_baseChange
      L K' vK wΩ hKΩ hhens hTame
  exact ⟨commonTarget, hRight, hTopTame, hRightBook, hTopBook⟩

/--
Finite tame base change on the actual compositum, in the direct CompleteDVF
API. If `L/K` is finite tame in the book presentation, then the valued
extension on `(L ⊔ K')/K'` is tamely ramified.
-/
theorem exists_actualCommonTop_isTamelyRamified_of_bookFiniteTame
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω]
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K']
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K K']
    {baseK : CompleteDVF.{u, v} K}
    {rightBase : CompleteDVF.{u, w} K'}
    [baseK.valuation.HasExtension rightBase.valuation]
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (wΩ : LubinTate.Valuations.ExponentialValuation Ω)
    (hKΩ : ∀ a : K, wΩ (algebraMap K Ω a) = vK a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    (hTame : FiniteTamelyRamifiedExtension vK
      (exponentialValuationRestrict wΩ L)
      (exponentialValuationRestrict_extends vK wΩ hKΩ L))
    (hBaseBook :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK =
        baseK.valuation.valuationSubring) :
    let Top := (L ⊔ K' : IntermediateField K Ω)
    ∃ commonTarget : CompleteDVF.{u, 0} Top,
      ∃ hRight : rightBase.valuation.HasExtension commonTarget.valuation,
        letI : rightBase.valuation.HasExtension commonTarget.valuation := hRight
        letI : FiniteDimensional K' Top :=
          finiteDimensional_sup_over_right L K'
        letI : Algebra.IsSeparable K' Top :=
          isSeparable_sup_over_right_of_left L K'
        letI : IsScalarTower rightBase.valuationSubring
            commonTarget.valuationSubring Top :=
          Valuation.valuationSubring_isScalarTower_of_hasExtension
            rightBase.valuation commonTarget.valuation
        IsTamelyRamified rightBase.toDVF commonTarget.toDVF := by
  let Top := (L ⊔ K' : IntermediateField K Ω)
  let wRight := exponentialValuationRestrict wΩ K'
  let wTop := exponentialValuationRestrict wΩ Top
  let hRightTop : ∀ a : K',
      wTop (algebraMap K' Top a) = wRight a := by
    intro a
    rfl
  let : FiniteDimensional K' Top :=
    finiteDimensional_sup_over_right L K'
  let : Algebra.IsSeparable K' Top :=
    isSeparable_sup_over_right_of_left L K'
  obtain ⟨commonTarget, hRight, hTopTame, hRightBook, hTopBook⟩ :=
    exists_actualCommonTop_bookFiniteTame_and_compatible
      (baseK := baseK) (rightBase := rightBase)
      L K' vK wΩ hKΩ hhens hTame hBaseBook
  let : rightBase.valuation.HasExtension commonTarget.valuation := hRight
  let : IsScalarTower rightBase.valuationSubring
      commonTarget.valuationSubring Top :=
    Valuation.valuationSubring_isScalarTower_of_hasExtension
      rightBase.valuation commonTarget.valuation
  have hBaseRight :=
    exponentialValuationRestrict_extends vK wΩ hKΩ K'
  have hhensRight : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wRight).valuation :=
    henselianValuation_of_algebraic_extension
      vK wRight hBaseRight hhens
  refine ⟨commonTarget, hRight, ?_⟩
  exact isTamelyRamified_of_bookFiniteTame
    (base := rightBase) (target := commonTarget)
    wRight wTop hRightTop hhensRight hTopTame hRightBook hTopBook

/-- Classical Abhyankar ramification-index absorption on the actual
compositum, expressed with canonical ramification indices.

The only compatibility input is at the original base.  Finite-separable
uniqueness identifies the book valuation rings on `L`, `K'`, and `L ⊔ K'`
with the three CompleteDVF presentations, so the source-producing Book value
group theorem transports to the canonical indices. -/
theorem exists_actualCommonTop_ramificationIndex_dvd_div_gcd_of_bookFiniteTame
    {K Omega : Type u} [Field K] [Field Omega] [Algebra K Omega]
    [Algebra.IsAlgebraic K Omega]
    (L K' : IntermediateField K Omega)
    [FiniteDimensional K L] [FiniteDimensional K K']
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K K']
    {baseK : CompleteDVF.{u, v} K}
    {rightBase : CompleteDVF.{u, w} K'}
    {leftTarget : CompleteDVF.{u, x} L}
    [baseK.valuation.HasExtension rightBase.valuation]
    [baseK.valuation.HasExtension leftTarget.valuation]
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (wOmega : LubinTate.Valuations.ExponentialValuation Omega)
    (hKOmega : forall a : K,
      wOmega (algebraMap K Omega a) = vK a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    (hTame : FiniteTamelyRamifiedExtension vK
      (exponentialValuationRestrict wOmega L)
      (exponentialValuationRestrict_extends vK wOmega hKOmega L))
    (hBaseBook :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK =
        baseK.valuation.valuationSubring) :
    let Top := (L ⊔ K' : IntermediateField K Omega)
    exists commonTarget : CompleteDVF.{u, 0} Top,
      exists hRight : rightBase.valuation.HasExtension commonTarget.valuation,
        letI : rightBase.valuation.HasExtension commonTarget.valuation := hRight
        letI : FiniteDimensional K' Top :=
          finiteDimensional_sup_over_right L K'
        letI : Algebra.IsSeparable K' Top :=
          isSeparable_sup_over_right_of_left L K'
        letI : IsScalarTower rightBase.valuationSubring
            commonTarget.valuationSubring Top :=
          Valuation.valuationSubring_isScalarTower_of_hasExtension
            rightBase.valuation commonTarget.valuation
        ramificationIndex rightBase.toDVF commonTarget.toDVF ∣
          ramificationIndex baseK.toDVF leftTarget.toDVF /
            Nat.gcd (ramificationIndex baseK.toDVF leftTarget.toDVF)
              (ramificationIndex baseK.toDVF rightBase.toDVF) := by
  let Top := (L ⊔ K' : IntermediateField K Omega)
  let wLeft := exponentialValuationRestrict wOmega L
  let wRight := exponentialValuationRestrict wOmega K'
  let wTop := exponentialValuationRestrict wOmega Top
  let hLeft :=
    exponentialValuationRestrict_extends vK wOmega hKOmega L
  let hBaseRight :=
    exponentialValuationRestrict_extends vK wOmega hKOmega K'
  let hRightTop : forall a : K',
      wTop (algebraMap K' Top a) = wRight a := by
    intro a
    rfl
  let : FiniteDimensional K' Top :=
    finiteDimensional_sup_over_right L K'
  let : Algebra.IsSeparable K' Top :=
    isSeparable_sup_over_right_of_left L K'
  obtain ⟨commonTarget, hRight, _hTopTame, hRightBook, hTopBook⟩ :=
    exists_actualCommonTop_bookFiniteTame_and_compatible
      (baseK := baseK) (rightBase := rightBase)
      L K' vK wOmega hKOmega hhens hTame hBaseBook
  let : rightBase.valuation.HasExtension commonTarget.valuation := hRight
  let : IsScalarTower rightBase.valuationSubring
      commonTarget.valuationSubring Top :=
    Valuation.valuationSubring_isScalarTower_of_hasExtension
      rightBase.valuation commonTarget.valuation
  have hBookLeftExt : baseK.valuation.HasExtension
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wLeft).valuation :=
    completeDVF_hasExtension_bookValuationSubring_of_eq
      baseK vK wLeft hLeft hBaseBook
  let : baseK.valuation.HasExtension
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wLeft).valuation :=
    hBookLeftExt
  have hLeftBook :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wLeft =
        leftTarget.valuation.valuationSubring := by
    simpa only [ValuationSubring.valuationSubring_valuation] using
      valuationSubring_eq_target_of_finite_separable baseK leftTarget
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wLeft).valuation
  have hTopSubring : LubinTate.Valuations.exponentialValuationSubring wTop =
      commonTarget.valuation.valuationSubring.toSubring :=
    congrArg ValuationSubring.toSubring hTopBook
  let : IsDiscreteValuationRing
      (LubinTate.Valuations.exponentialValuationSubring wTop) := by
    rw [hTopSubring]
    exact commonTarget.valuationSubring_isDiscreteValuationRing
  have hwTopDiscrete : LubinTate.Valuations.DiscreteExponentialValuation wTop :=
    discreteExponentialValuation_of_isDiscreteValuationRing wTop
  have hbook :=
    bookRamificationIndex_commonTop_dvd_div_gcd_of_finiteTame
      L K' vK wOmega hKOmega hhens hTame hwTopDiscrete
  have hramRight : exponentialRamificationIndex wRight wTop =
      ramificationIndex rightBase.toDVF commonTarget.toDVF :=
    RamificationTheory.exponentialRamificationIndex_eq_ramificationIndex_of_valuationSubrings_eq
      wRight wTop hRightTop hRightBook hTopBook
  have hramLeft : exponentialRamificationIndex vK wLeft =
      ramificationIndex baseK.toDVF leftTarget.toDVF :=
    RamificationTheory.exponentialRamificationIndex_eq_ramificationIndex_of_valuationSubrings_eq
      vK wLeft hLeft hBaseBook hLeftBook
  have hramBase : exponentialRamificationIndex vK wRight =
      ramificationIndex baseK.toDVF rightBase.toDVF :=
    RamificationTheory.exponentialRamificationIndex_eq_ramificationIndex_of_valuationSubrings_eq
      vK wRight hBaseRight hBaseBook hRightBook
  change exponentialRamificationIndex wRight wTop ∣
      exponentialRamificationIndex vK wLeft /
        Nat.gcd (exponentialRamificationIndex vK wLeft)
          (exponentialRamificationIndex vK wRight) at hbook
  rw [hramRight, hramLeft, hramBase] at hbook
  refine ⟨commonTarget, hRight, ?_⟩
  exact hbook

/-- Classical Abhyankar's lemma on the actual compositum: if the finite
base change absorbs the original tame ramification index, the upper-right
valued extension is unramified. -/
theorem exists_actualCommonTop_isUnramified_of_bookFiniteTame_of_dvd
    {K Omega : Type u} [Field K] [Field Omega] [Algebra K Omega]
    [Algebra.IsAlgebraic K Omega]
    (L K' : IntermediateField K Omega)
    [FiniteDimensional K L] [FiniteDimensional K K']
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K K']
    {baseK : CompleteDVF.{u, v} K}
    {rightBase : CompleteDVF.{u, w} K'}
    {leftTarget : CompleteDVF.{u, x} L}
    [baseK.valuation.HasExtension rightBase.valuation]
    [baseK.valuation.HasExtension leftTarget.valuation]
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (wOmega : LubinTate.Valuations.ExponentialValuation Omega)
    (hKOmega : forall a : K,
      wOmega (algebraMap K Omega a) = vK a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK).valuation)
    (hTame : FiniteTamelyRamifiedExtension vK
      (exponentialValuationRestrict wOmega L)
      (exponentialValuationRestrict_extends vK wOmega hKOmega L))
    (hBaseBook :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK =
        baseK.valuation.valuationSubring)
    (hdiv : ramificationIndex baseK.toDVF leftTarget.toDVF ∣
      ramificationIndex baseK.toDVF rightBase.toDVF) :
    let Top := (L ⊔ K' : IntermediateField K Omega)
    exists commonTarget : CompleteDVF.{u, 0} Top,
      exists hRight : rightBase.valuation.HasExtension commonTarget.valuation,
        letI : rightBase.valuation.HasExtension commonTarget.valuation := hRight
        letI : FiniteDimensional K' Top :=
          finiteDimensional_sup_over_right L K'
        letI : Algebra.IsSeparable K' Top :=
          isSeparable_sup_over_right_of_left L K'
        letI : IsScalarTower rightBase.valuationSubring
            commonTarget.valuationSubring Top :=
          Valuation.valuationSubring_isScalarTower_of_hasExtension
            rightBase.valuation commonTarget.valuation
        IsUnramified rightBase.toDVF commonTarget.toDVF := by
  let Top := (L ⊔ K' : IntermediateField K Omega)
  let wLeft := exponentialValuationRestrict wOmega L
  let hLeft :=
    exponentialValuationRestrict_extends vK wOmega hKOmega L
  let : FiniteDimensional K' Top :=
    finiteDimensional_sup_over_right L K'
  let : Algebra.IsSeparable K' Top :=
    isSeparable_sup_over_right_of_left L K'
  obtain ⟨commonTarget, hRight, hbound⟩ :=
    exists_actualCommonTop_ramificationIndex_dvd_div_gcd_of_bookFiniteTame
      (baseK := baseK) (rightBase := rightBase)
      (leftTarget := leftTarget)
      L K' vK wOmega hKOmega hhens hTame hBaseBook
  let : rightBase.valuation.HasExtension commonTarget.valuation := hRight
  let : IsScalarTower rightBase.valuationSubring
      commonTarget.valuationSubring Top :=
    Valuation.valuationSubring_isScalarTower_of_hasExtension
      rightBase.valuation commonTarget.valuation
  have hBookLeftExt : baseK.valuation.HasExtension
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wLeft).valuation :=
    completeDVF_hasExtension_bookValuationSubring_of_eq
      baseK vK wLeft hLeft hBaseBook
  let : baseK.valuation.HasExtension
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wLeft).valuation :=
    hBookLeftExt
  have hLeftBook :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wLeft =
        leftTarget.valuation.valuationSubring := by
    simpa only [ValuationSubring.valuationSubring_valuation] using
      valuationSubring_eq_target_of_finite_separable baseK leftTarget
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wLeft).valuation
  have hramLeft : exponentialRamificationIndex vK wLeft =
      ramificationIndex baseK.toDVF leftTarget.toDVF :=
    RamificationTheory.exponentialRamificationIndex_eq_ramificationIndex_of_valuationSubrings_eq
      vK wLeft hLeft hBaseBook hLeftBook
  have hleftPos :
      0 < ramificationIndex baseK.toDVF leftTarget.toDVF := by
    rw [← hramLeft]
    exact bookRamificationIndex_pos vK wLeft hLeft
  refine ⟨commonTarget, hRight, ?_⟩
  change ramificationIndex rightBase.toDVF commonTarget.toDVF = 1
  exact eq_one_of_abhyankarIndexBound_of_dvd
    hleftPos hbound hdiv

end TameAbhyankar

end
