/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal
public import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealGroup
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Nyll.ClassFieldTheory.Algebra.FractionalIdealFactorization

/-!
# Prime factorization of nonzero fractional ideals

Mathlib's `FractionalIdeal.count` and unique-factorization theorems identify
the multiplicative group of nonzero fractional ideals with the finitely
supported integer exponents of finite primes. This equivalence is formulated
entirely in Mathlib and public Definitions vocabulary.
-/



@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

namespace NumberFieldFractionalIdealGroup

variable {K : Type u} [Field K] [NumberField K]

/-- The homomorphism sending an integer exponent to the corresponding
power of a finite prime. -/
noncomputable def primePowerHom (v : HeightOneSpectrum (𝓞 K)) :
    Multiplicative ℤ →* NumberFieldFractionalIdealGroup K :=
  ClassFieldTheory.FractionalIdealFactorization.primePowerHom (F := K) v

/-- Reconstruct a fractional ideal from its finitely supported vector
of prime exponents. -/
noncomputable def factorization :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) →*
      NumberFieldFractionalIdealGroup K :=
  ClassFieldTheory.FractionalIdealFactorization.factorization (R := 𝓞 K) (F := K)

@[simp]
theorem factorization_val (exps :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ)) :
    ((factorization exps : NumberFieldFractionalIdealGroup K) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      exps.toAdd.prod fun v n =>
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n :=
  ClassFieldTheory.FractionalIdealFactorization.factorization_val exps

/-- Only finitely many finite primes occur with nonzero exponent in a
nonzero fractional ideal. -/
theorem finite_count_support (I : NumberFieldFractionalIdealGroup K) :
    {v : HeightOneSpectrum (𝓞 K) |
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0}.Finite :=
  ClassFieldTheory.FractionalIdealFactorization.finite_count_support I

/-- The finitely supported vector of prime exponents of a nonzero
fractional ideal. -/
noncomputable def countVector (I : NumberFieldFractionalIdealGroup K) :
    HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  ClassFieldTheory.FractionalIdealFactorization.countVector I

@[simp]
theorem countVector_apply (I : NumberFieldFractionalIdealGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    countVector I v =
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
  ClassFieldTheory.FractionalIdealFactorization.countVector_apply I v

@[simp]
theorem count_factorization (exps :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ))
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      ((factorization exps : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      exps.toAdd v :=
  ClassFieldTheory.FractionalIdealFactorization.count_factorization exps v

theorem ext_count {I J : NumberFieldFractionalIdealGroup K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      FractionalIdeal.count K v
        (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) :
    I = J :=
  ClassFieldTheory.FractionalIdealFactorization.ext_count h

theorem factorization_injective :
    Function.Injective (factorization (K := K)) :=
  ClassFieldTheory.FractionalIdealFactorization.factorization_injective

theorem factorization_surjective :
    Function.Surjective (factorization (K := K)) :=
  ClassFieldTheory.FractionalIdealFactorization.factorization_surjective

/-- Multiplicative unique factorization of nonzero fractional ideals by
finite primes. -/
noncomputable def factorizationEquiv :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) ≃*
      NumberFieldFractionalIdealGroup K :=
  ClassFieldTheory.FractionalIdealFactorization.factorizationEquiv (R := 𝓞 K) (F := K)

/-- The inverse factorization map is the actual prime-count vector. -/
@[simp]
theorem factorizationEquiv_symm_toAdd (I : NumberFieldFractionalIdealGroup K) :
    ((factorizationEquiv (K := K)).symm I).toAdd = countVector I :=
  ClassFieldTheory.FractionalIdealFactorization.factorizationEquiv_symm_toAdd I

end NumberFieldFractionalIdealGroup

end ClassFieldTheory
