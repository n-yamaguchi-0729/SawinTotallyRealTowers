/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalField
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedValue
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# The valued extension at a specified pair of finite places

The canonical completed embedding preserves the distinguished valuation rings.
Its ramification index is the ordinary index of those actual local rings.
-/

@[expose] public section

open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

variable (K : Type u) (L : Type v)
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The canonical completed embedding extends the canonical valuation relation. -/
theorem finitePlaceCompletion_hasExtension
    (v : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v}) :
    let : Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v W).toAlgebra
    let : ValuativeRel (v.adicCompletion K) := finitePlaceCompletionValuativeRel K v
    let : ValuativeRel (W.1.adicCompletion L) := finitePlaceCompletionValuativeRel L W.1
    (ValuativeRel.valuation (v.adicCompletion K)).HasExtension
      (ValuativeRel.valuation (W.1.adicCompletion L)) := by
  intro completionAlgebra baseRelation targetRelation
  let νK : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)) := Valued.v
  let νL : Valuation (W.1.adicCompletion L) (WithZero (Multiplicative ℤ)) := Valued.v
  let : νK.Compatible := Valuation.Compatible.ofValuation νK
  let : νL.Compatible := Valuation.Compatible.ofValuation νL
  let : W.1.asIdeal.LiesOver v.asIdeal :=
    ⟨congrArg HeightOneSpectrum.asIdeal W.2.symm⟩
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change ValuativeRel.valuation (W.1.adicCompletion L)
      (algebraMap (v.adicCompletion K) (W.1.adicCompletion L) x) ≤ 1 ↔
    ValuativeRel.valuation (v.adicCompletion K) x ≤ 1
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (W.1.adicCompletion L))
      νL).le_one_iff_le_one,
    (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
      νK).le_one_iff_le_one]
  have hmap : νL (algebraMap (v.adicCompletion K) (W.1.adicCompletion L) x) =
      νK x ^ W.1.asIdeal.ramificationIdx (𝓞 K) := by
    have h := finitePlaceAdicCompletionMap_valued K L v W x
    rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal W.1.asIdeal v.ne_bot] at h
    exact h
  rw [hmap, pow_le_one_iff (W.1.asIdeal.ramificationIdx_pos (𝓞 K)).ne']

/-- The ramification index of the canonical extension of completed integer rings. -/
def finitePlaceCompletionRamificationIndex
    (v : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v}) : ℕ :=
  let : Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L v W).toAlgebra
  let : ValuativeRel (v.adicCompletion K) := finitePlaceCompletionValuativeRel K v
  let : ValuativeRel (W.1.adicCompletion L) := finitePlaceCompletionValuativeRel L W.1
  let : (ValuativeRel.valuation (v.adicCompletion K)).HasExtension
      (ValuativeRel.valuation (W.1.adicCompletion L)) :=
    finitePlaceCompletion_hasExtension K L v W
  (𝓂[W.1.adicCompletion L] : Ideal 𝒪[W.1.adicCompletion L]).ramificationIdx
    𝒪[v.adicCompletion K]

/-- Completing at a specified pair of finite places preserves the actual
ramification index of the prime ideal. -/
theorem finitePlaceCompletionRamificationIndex_eq
    (v : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v}) :
    finitePlaceCompletionRamificationIndex K L v W =
      W.1.asIdeal.ramificationIdx (𝓞 K) := by
  let F := v.adicCompletion K
  let E := W.1.adicCompletion L
  let : Algebra F E := (finitePlaceAdicCompletionMap K L v W).toAlgebra
  let : ValuativeRel F := finitePlaceCompletionValuativeRel K v
  let : ValuativeRel E := finitePlaceCompletionValuativeRel L W.1
  let : IsNonarchimedeanLocalField F := finitePlaceCompletionIsNonarchimedeanLocalField K v
  let : IsNonarchimedeanLocalField E := finitePlaceCompletionIsNonarchimedeanLocalField L W.1
  let : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation E) :=
    finitePlaceCompletion_hasExtension K L v W
  let : FiniteDimensional F E := finitePlaceAdicCompletionMap_moduleFinite K L v W
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let : Algebra.IsIntegral F E := Algebra.IsIntegral.of_finite F E
  let : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  let : Algebra 𝒪[F] E := Algebra.ofSubsemiring 𝒪[F]
  let : IsIntegralClosure 𝒪[E] 𝒪[F] E :=
    LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure F E
  let νF : Valuation F (WithZero (Multiplicative ℤ)) := Valued.v
  let νE : Valuation E (WithZero (Multiplicative ℤ)) := Valued.v
  let : νF.Compatible := Valuation.Compatible.ofValuation νF
  let : νE.Compatible := Valuation.Compatible.ofValuation νE
  have hνF : Function.Surjective νF := v.valuedAdicCompletion_surjective K
  have hνE : Function.Surjective νE := W.1.valuedAdicCompletion_surjective L
  let : W.1.asIdeal.LiesOver v.asIdeal :=
    ⟨congrArg HeightOneSpectrum.asIdeal W.2.symm⟩
  obtain ⟨π, hπ⟩ := LocalFieldTheory.IsNonarchimedeanLocalField.v_uniformiser F
  have hlogπ : WithZero.log (νF (π : F)) = 1 :=
    (LocalFieldTheory.normalizedValue_eq_withZeroLog_of_surjective F νF hνF π).symm.trans hπ
  have hscale :=
    LocalClassFieldTheory.v_mapBaseUnitsToExtensionUnits_eq_ramificationIdx_mul F E π
  rw [hπ, mul_one,
    LocalFieldTheory.normalizedValue_eq_withZeroLog_of_surjective E νE hνE] at hscale
  change WithZero.log (νE (finitePlaceAdicCompletionMap K L v W (π : F))) =
    ((𝓂[E] : Ideal 𝒪[E]).ramificationIdx 𝒪[F] : ℤ) at hscale
  have hmap := finitePlaceAdicCompletionMap_valued K L v W (π : F)
  rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal W.1.asIdeal v.ne_bot] at hmap
  change νE (finitePlaceAdicCompletionMap K L v W (π : F)) =
    νF (π : F) ^ W.1.asIdeal.ramificationIdx (𝓞 K) at hmap
  rw [hmap, WithZero.log_pow, nsmul_eq_mul, hlogπ, mul_one] at hscale
  change (𝓂[E] : Ideal 𝒪[E]).ramificationIdx 𝒪[F] =
    W.1.asIdeal.ramificationIdx (𝓞 K)
  exact_mod_cast hscale.symm

end ClassFieldTheory
