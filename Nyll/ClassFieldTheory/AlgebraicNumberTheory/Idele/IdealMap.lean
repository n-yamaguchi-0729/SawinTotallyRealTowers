/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMapCore
public import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealFactorization
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The ideal attached to an idele

This file formalizes the ideal map from ideles. Its construction
is explicit: local discrete valuations form a finitely supported integer
vector, and unique factorization of fractional ideals identifies that vector
with a nonzero fractional ideal.  We prove both stages surjective and identify
the kernel with the ideles integral at every finite place.
-/



@[expose] public section

open scoped NumberField RestrictedProduct WithZero
open ClassFieldTheory
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace FiniteIdeleGroup

/-- The exponent of a local multiplicative element, normalized so that a
uniformizer has exponent one. -/
def localOrder (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* Multiplicative ℤ :=
  RestrictedProduct.DiscreteValuation.localOrder (v.adicCompletion K)

@[simp]
theorem localOrder_apply (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    (localOrder v x).toAdd =
      -WithZero.log (Valued.v (x : v.adicCompletion K)) :=
  RestrictedProduct.DiscreteValuation.localOrder_apply (v.adicCompletion K) x

@[simp]
theorem localOrder_eq_zero_iff (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    (localOrder v x).toAdd = 0 ↔
      x ∈ (v.adicCompletionIntegers K).units :=
  RestrictedProduct.DiscreteValuation.localOrder_eq_zero_iff (v.adicCompletion K) x

/-- The set of finite places where a finite idele is not an integral unit is
finite. -/
theorem finite_nonLocalUnits (a : FiniteIdeleGroup K) :
    {v : HeightOneSpectrum (𝓞 K) |
      a v ∉ (v.adicCompletionIntegers K).units}.Finite :=
  RestrictedProduct.DiscreteValuation.finite_nonLocalUnits
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) a

/-- The finitely supported family of normalized local orders of a finite
idele. -/
def valuationVectorAdd (a : FiniteIdeleGroup K) :
    HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  RestrictedProduct.DiscreteValuation.valuationVectorAdd
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) a

@[simp]
theorem valuationVectorAdd_apply (a : FiniteIdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    valuationVectorAdd a v = (localOrder v (a v)).toAdd :=
  RestrictedProduct.DiscreteValuation.valuationVectorAdd_apply
    (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) a v

/-- The finite valuation vector is a homomorphism from finite ideles to the
free abelian group on finite places. -/
def valuationVector :
    FiniteIdeleGroup K →* Multiplicative
      (HeightOneSpectrum (𝓞 K) →₀ ℤ) :=
  RestrictedProduct.DiscreteValuation.valuationVector
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)

@[simp]
theorem valuationVector_apply (a : FiniteIdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    (valuationVector a).toAdd v =
      (localOrder v (a v)).toAdd :=
  RestrictedProduct.DiscreteValuation.valuationVector_apply
    (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) a v

/-- A chosen local element of prescribed normalized order. -/
def chosenLocalOrderSection (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (v.adicCompletion K)ˣ :=
  RestrictedProduct.DiscreteValuation.chosenLocalOrderSection (v.adicCompletion K)
    (HeightOneSpectrum.valuedAdicCompletion_surjective K v) n

@[simp]
theorem localOrder_chosenLocalOrderSection
    (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (localOrder v (chosenLocalOrderSection v n)).toAdd = n :=
  RestrictedProduct.DiscreteValuation.localOrder_chosenLocalOrderSection
    (v.adicCompletion K) (HeightOneSpectrum.valuedAdicCompletion_surjective K v) n

/-- A finite idele with a prescribed finitely supported valuation vector. -/
def valuationVectorSection
    (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    FiniteIdeleGroup K :=
  RestrictedProduct.DiscreteValuation.valuationVectorSection
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => HeightOneSpectrum.valuedAdicCompletion_surjective K v) e

@[simp]
theorem valuationVector_valuationVectorSection
    (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    valuationVector (valuationVectorSection e) =
      Multiplicative.ofAdd e :=
  RestrictedProduct.DiscreteValuation.valuationVector_valuationVectorSection
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => HeightOneSpectrum.valuedAdicCompletion_surjective K v) e

theorem valuationVector_surjective :
    Function.Surjective (valuationVector (K := K)) :=
  RestrictedProduct.DiscreteValuation.valuationVector_surjective
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => HeightOneSpectrum.valuedAdicCompletion_surjective K v)

end FiniteIdeleGroup


namespace FiniteIdeleGroup

/-- The fractional ideal attached to a finite idele. -/
def fractionalIdeal : FiniteIdeleGroup K →* NumberFieldFractionalIdealGroup K :=
  NumberFieldFractionalIdealGroup.factorizationEquiv.toMonoidHom.comp valuationVector

/-- The ideal map is evaluated by the normalized valuation vector. -/
theorem fractionalIdeal_eq_factorization (a : FiniteIdeleGroup K) :
    fractionalIdeal a =
      NumberFieldFractionalIdealGroup.factorizationEquiv (valuationVector a) :=
  rfl

theorem fractionalIdeal_surjective : Function.Surjective (fractionalIdeal (K := K)) :=
  NumberFieldFractionalIdealGroup.factorizationEquiv.surjective.comp valuationVector_surjective

/-- Finite ideles integral at every finite place. -/
def integralSubgroup : Subgroup (FiniteIdeleGroup K) :=
  RestrictedProduct.DiscreteValuation.integralSubgroup
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)

@[simp]
theorem mem_integralSubgroup_iff (a : FiniteIdeleGroup K) :
    a ∈ integralSubgroup ↔
      ∀ v : HeightOneSpectrum (𝓞 K),
        a v ∈ (v.adicCompletionIntegers K).units :=
  Iff.rfl

theorem fractionalIdeal_ker : (fractionalIdeal (K := K)).ker = integralSubgroup := by
  ext a
  change NumberFieldFractionalIdealGroup.factorizationEquiv (valuationVector a) = 1 ↔
    a ∈ integralSubgroup
  rw [← map_one (NumberFieldFractionalIdealGroup.factorizationEquiv (K := K)),
    MulEquiv.apply_eq_iff_eq]
  exact RestrictedProduct.DiscreteValuation.valuationVector_eq_one_iff
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) a

/-- The ideal group as the quotient of finite ideles by the everywhere
integral finite ideles. -/
def quotientIntegralEquiv :
    FiniteIdeleGroup K ⧸ integralSubgroup ≃*
      NumberFieldFractionalIdealGroup K := by
  rw [← fractionalIdeal_ker]
  exact QuotientGroup.quotientKerEquivOfSurjective
    fractionalIdeal fractionalIdeal_surjective

end FiniteIdeleGroup

namespace IdeleGroup

/-- The fractional ideal attached to an idele. The archimedean
components do not contribute. -/
abbrev fractionalIdeal : IdeleGroup K →* NumberFieldFractionalIdealGroup K :=
  NumberField.IdeleGroup.fractionalIdeal (R := 𝓞 K) (K := K)

theorem fractionalIdeal_surjective : Function.Surjective (fractionalIdeal (K := K)) :=
  NumberField.IdeleGroup.fractionalIdeal_surjective (R := 𝓞 K) (K := K)

/-- Ideles integral at every finite place. -/
abbrev integralAtFinitePlaces : Subgroup (IdeleGroup K) :=
  NumberField.IdeleGroup.integralAtFinitePlaces (R := 𝓞 K) (K := K)

theorem fractionalIdeal_ker : (fractionalIdeal (K := K)).ker = integralAtFinitePlaces :=
  NumberField.IdeleGroup.fractionalIdeal_ker (R := 𝓞 K) (K := K)

/-- The ideal group as the quotient of all ideles by those integral at
every finite place. -/
def quotientIntegralEquiv :
    IdeleGroup K ⧸ integralAtFinitePlaces ≃*
      NumberFieldFractionalIdealGroup K := by
  rw [← fractionalIdeal_ker]
  exact QuotientGroup.quotientKerEquivOfSurjective
    fractionalIdeal fractionalIdeal_surjective

/-- The canonical surjection from ideles to the ordinary ideal class group. -/
abbrev idealClass : IdeleGroup K →* ClassGroup (𝓞 K) :=
  NumberField.IdeleGroup.idealClass (R := 𝓞 K) (K := K)

theorem idealClass_surjective : Function.Surjective (idealClass (K := K)) :=
  NumberField.IdeleGroup.idealClass_surjective (R := 𝓞 K) (K := K)

/-- A quotient form of the ideal-class map. The following results identify
this kernel with `I_K^{S∞} Kˣ`. -/
def quotientIdealClassKernelEquiv :
    IdeleGroup K ⧸ (idealClass (K := K)).ker ≃*
      ClassGroup (𝓞 K) :=
  QuotientGroup.quotientKerEquivOfSurjective
    idealClass idealClass_surjective

end IdeleGroup
