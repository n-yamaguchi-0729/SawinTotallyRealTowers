/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalField
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalFieldExtension
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedValue
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.ValuedFieldTheory.LocalField.NormUnits

/-!
# Local orders of finite-place norms

For a finite extension of number fields and a place upstairs, the order of
the concrete local field norm is the inertia degree times the upstairs
order.  The proof uses the actual norm–valuation theorem for finite separable
local-field extensions.  The two normalization comparisons needed here are
also concrete:

* the intrinsic local-field valuation is compared with the distinguished
  `ℤᵐ⁰`-valued completion valuation;
* the residue degree of the completed extension is identified with the
  inertia degree of the corresponding prime of the number-field extension.
-/



@[expose] public section

open scoped NumberField ValuativeRel WithZero
open NumberField IsDedekindDomain

noncomputable section

namespace FiniteIdeleGroup

universe u v w

/-- Identity on the underlying field gives the equivalence between the
intrinsic valuation ring and the distinguished valued-field integer ring. -/
private noncomputable def intrinsicIntegerEquivValuedInteger
    (F : Type w)
    [Field F] [ValuativeRel F]
    [Valued F (WithZero (Multiplicative ℤ))]
    [(Valued.v :
      Valuation F (WithZero (Multiplicative ℤ))).Compatible] :
    𝒪[F] ≃+* Valued.integer F := by
  apply RingEquiv.subringCongr
  exact congrArg ValuationSubring.toSubring <|
    (Valuation.isEquiv_iff_valuationSubring
      (ValuativeRel.valuation F)
      (Valued.v : Valuation F (WithZero (Multiplicative ℤ)))).mp <|
      ValuativeRel.isEquiv
        (ValuativeRel.valuation F)
        (Valued.v :
          Valuation F (WithZero (Multiplicative ℤ)))

/-- The residue field for the intrinsic valuation is the residue field of
the distinguished `ℤᵐ⁰`-valued completion valuation. -/
private noncomputable def intrinsicResidueFieldEquivValuedResidueField
    (F : Type w)
    [Field F] [ValuativeRel F]
    [Valued F (WithZero (Multiplicative ℤ))]
    [(Valued.v :
      Valuation F (WithZero (Multiplicative ℤ))).Compatible] :
    𝓀[F] ≃+* Valued.ResidueField F :=
  IsLocalRing.ResidueField.mapEquiv
    (intrinsicIntegerEquivValuedInteger F)


private theorem absNorm_eq_card_intrinsicAdicResidueField
    (K : Type u) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    [ValuativeRel (v.adicCompletion K)]
    [(Valued.v :
      Valuation (v.adicCompletion K)
        (WithZero (Multiplicative ℤ))).Compatible] :
    Ideal.absNorm v.asIdeal =
      Nat.card 𝓀[v.adicCompletion K] := by
  calc
    Ideal.absNorm v.asIdeal =
        Nat.card
          (Valued.ResidueField (v.adicCompletion K)) := by
      rw [Ideal.absNorm_apply]
      exact
        Nat.card_congr
          (GlobalClassFieldTheory.ClassFieldAxiom.ringOfIntegersQuotientEquivAdicResidueField
            (K := K) v).toEquiv
    _ = Nat.card 𝓀[v.adicCompletion K] := by
      exact
        (Nat.card_congr
          (intrinsicResidueFieldEquivValuedResidueField
            (v.adicCompletion K)).toEquiv).symm

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- The local order of the actual norm between finite-place completions is
multiplied by the inertia degree of the upstairs prime. -/
theorem localOrder_normUnits
    (v₀ : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀})
    (x : (W.1.adicCompletion L)ˣ) :
    let _ : Algebra
        (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
    (localOrder v₀
      (LocalFieldTheory.normUnits
        (v₀.adicCompletion K) (W.1.adicCompletion L) x)).toAdd =
      (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
        (localOrder W.1 x).toAdd := by
  intro completionAlgebra
  classical
  let F := v₀.adicCompletion K
  let E := W.1.adicCompletion L
  let : IsScalarTower K F E :=
    finitePlaceAdicCompletionMap_isScalarTower K L v₀ W
  let : FiniteDimensional F E :=
    finitePlaceAdicCompletionMap_moduleFinite K L v₀ W
  let : CharZero F :=
    charZero_of_injective_algebraMap
      (algebraMap K F).injective
  let : Algebra.IsIntegral F E :=
    Algebra.IsIntegral.of_finite F E
  let : Algebra.IsSeparable F E :=
    Algebra.IsSeparable.of_integral F E
  let νF : Valuation F (WithZero (Multiplicative ℤ)) :=
    Valued.v
  let νE : Valuation E (WithZero (Multiplicative ℤ)) :=
    Valued.v
  have hνF : Function.Surjective νF := by
    simpa [F, νF] using
      v₀.valuedAdicCompletion_surjective K
  have hνE : Function.Surjective νE := by
    simpa [E, νE] using
      W.1.valuedAdicCompletion_surjective L
  let : ValuativeRel F :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel K v₀
  let : ValuativeRel E :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel L W.1
  let : νF.Compatible := Valuation.Compatible.ofValuation νF
  let : νE.Compatible := Valuation.Compatible.ofValuation νE
  let : IsNonarchimedeanLocalField F :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField K v₀
  let : IsNonarchimedeanLocalField E :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField L W.1
  let ν₀F := ValuativeRel.valuation F
  let ν₀E := ValuativeRel.valuation E
  let : W.1.asIdeal.LiesOver v₀.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal W.2.symm
  let : ν₀F.HasExtension ν₀E :=
    ClassFieldTheory.finitePlaceCompletion_hasExtension K L v₀ W
  let : Algebra 𝒪[F] E :=
    Algebra.ofSubsemiring 𝒪[F]
  let : IsIntegralClosure 𝒪[E] 𝒪[F] E :=
    LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure F E
  have hNormValue :=
    LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparable
      F E x
  rw [
    LocalFieldTheory.normalizedValue_eq_withZeroLog_of_surjective
      F νF hνF
        (LocalFieldTheory.normUnits F E x),
    LocalFieldTheory.normalizedValue_eq_withZeroLog_of_surjective
      E νE hνE x
  ] at hNormValue
  have hResidueDegree :
      Module.finrank 𝓀[F] 𝓀[E] =
        W.1.asIdeal.inertiaDeg (𝓞 K) := by
    apply
      Nat.pow_right_injective
        (Nat.succ_le_iff.mpr
          (HeightOneSpectrum.one_lt_absNorm v₀))
    calc
      Ideal.absNorm v₀.asIdeal ^
            Module.finrank 𝓀[F] 𝓀[E] =
          Nat.card 𝓀[F] ^
            Module.finrank 𝓀[F] 𝓀[E] := by
              rw [
                absNorm_eq_card_intrinsicAdicResidueField
                  K v₀
              ]
      _ = Nat.card 𝓀[E] :=
        Module.natCard_eq_pow_finrank.symm
      _ = Ideal.absNorm W.1.asIdeal := by
        rw [
          absNorm_eq_card_intrinsicAdicResidueField
            L W.1
        ]
      _ =
          Ideal.absNorm v₀.asIdeal ^
            W.1.asIdeal.inertiaDeg (𝓞 K) := by
        exact
          (Ideal.absNorm_pow_inertiaDeg
            v₀.asIdeal W.1.asIdeal).symm
  rw [hResidueDegree] at hNormValue
  rw [localOrder_apply, localOrder_apply]
  change
    -WithZero.log
        (νF
          (LocalFieldTheory.normUnits F E x : F)) =
      (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
        -WithZero.log (νE (x : E))
  calc
    -WithZero.log
          (νF
            (LocalFieldTheory.normUnits F E x : F)) =
        -((W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
          WithZero.log (νE (x : E))) := by
            rw [hNormValue]
    _ =
        (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
          -WithZero.log (νE (x : E)) := by
            ring

end FiniteIdeleGroup

end
