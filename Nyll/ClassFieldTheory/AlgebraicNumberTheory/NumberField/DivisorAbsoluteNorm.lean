/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.FractionalIdealFactorization
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.FractionalIdeal.Norm

/-!
# Positive absolute norms of number-field divisors

The prime-power product and the fractional-ideal norm agree under unique
factorization. These arithmetic maps do not depend on any idele presentation.
-/

@[expose] public section

open scoped NumberField NNReal
open IsDedekindDomain ClassFieldTheory.FractionalIdealFactorization

noncomputable section

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The positive real unit given by the absolute norm of a finite prime. -/
def finitePrimeNorm (v : HeightOneSpectrum (𝓞 K)) : ℝ≥0ˣ :=
  Units.mk0 (v.asIdeal.absNorm : ℝ≥0)
    (HeightOneSpectrum.absNorm_ne_zero v)

/-- The homomorphism sending an integer exponent to the corresponding
power of the absolute norm of a finite prime. -/
def finitePrimeNormPowerHom (v : HeightOneSpectrum (𝓞 K)) :
    Multiplicative ℤ →* ℝ≥0ˣ :=
  MonoidHom.mk' (fun n => finitePrimeNorm v ^ n.toAdd)
    fun m n => by simp only [toAdd_mul, zpow_add]

/-- The norm of a finitely supported divisor. -/
def divisorAbsoluteNorm :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) →* ℝ≥0ˣ :=
  MonoidHom.mk' (fun exps =>
      exps.toAdd.prod fun v n =>
        finitePrimeNormPowerHom v (Multiplicative.ofAdd n))
    fun _ _ => Finsupp.prod_hom_add_index
      (fun v => finitePrimeNormPowerHom v)

/-- The positive absolute norm of a nonzero fractional ideal. -/
def fractionalIdealAbsoluteNorm :
    (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ →* ℝ≥0ˣ where
  toFun I :=
    Units.mk0
      ⟨(FractionalIdeal.absNorm
          (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ),
        Rat.cast_nonneg.mpr
          (FractionalIdeal.absNorm_nonneg
            (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))⟩
      (by
        intro h
        have hr := congrArg (fun z : ℝ≥0 => z.1) h
        change
          ((FractionalIdeal.absNorm
            (I : FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) = 0 at hr
        have hq : FractionalIdeal.absNorm
            (I : FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K) = 0 := by
          exact_mod_cast hr
        exact Units.ne_zero I
          (FractionalIdeal.absNorm_eq_zero_iff.mp hq))
  map_one' := by
    apply Units.ext
    apply NNReal.eq
    change
      ((FractionalIdeal.absNorm
        (1 : FractionalIdeal
          (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) = 1
    rw [FractionalIdeal.absNorm_one]
    norm_num
  map_mul' I J := by
    apply Units.ext
    change
      (⟨(FractionalIdeal.absNorm
          ((I * J : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ),
        Rat.cast_nonneg.mpr
          (FractionalIdeal.absNorm_nonneg
            ((I * J : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
              FractionalIdeal (nonZeroDivisors (𝓞 K)) K))⟩ : ℝ≥0) =
      ⟨(FractionalIdeal.absNorm
          (I : FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K) : ℝ),
        Rat.cast_nonneg.mpr
          (FractionalIdeal.absNorm_nonneg
            (I : FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K))⟩ *
      ⟨(FractionalIdeal.absNorm
          (J : FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K) : ℝ),
        Rat.cast_nonneg.mpr
          (FractionalIdeal.absNorm_nonneg
            (J : FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K))⟩
    apply NNReal.eq
    change
      ((FractionalIdeal.absNorm
        ((I * J : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) =
      ((FractionalIdeal.absNorm
        (I : FractionalIdeal
          (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) *
      ((FractionalIdeal.absNorm
        (J : FractionalIdeal
          (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ)
    norm_cast
    simpa only [Units.val_mul] using
      (map_mul FractionalIdeal.absNorm
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
        (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))

@[simp]
theorem fractionalIdealAbsoluteNorm_prime (v : HeightOneSpectrum (𝓞 K)) :
    fractionalIdealAbsoluteNorm (prime v) = finitePrimeNorm v := by
  apply Units.ext
  apply NNReal.eq
  change
    ((FractionalIdeal.absNorm
      (v.asIdeal :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) =
      (v.asIdeal.absNorm : ℝ)
  rw [FractionalIdeal.coeIdeal_absNorm]
  norm_cast

/-- The explicit prime-factor norm commutes with the factorization of a
fractional ideal. -/
theorem fractionalIdealAbsoluteNorm_factorization
    (e : Multiplicative
      (HeightOneSpectrum (𝓞 K) →₀ ℤ)) :
    fractionalIdealAbsoluteNorm (factorization e) =
      divisorAbsoluteNorm e := by
  change fractionalIdealAbsoluteNorm
      (e.toAdd.prod fun v n => primePowerHom (F := K) v
        (Multiplicative.ofAdd n)) =
    e.toAdd.prod fun v n =>
      finitePrimeNormPowerHom v
        (Multiplicative.ofAdd n)
  rw [map_finsuppProd]
  apply Finsupp.prod_congr
  intro v hv
  change fractionalIdealAbsoluteNorm (prime v ^ e.toAdd v) =
    finitePrimeNorm v ^ e.toAdd v
  rw [map_zpow, fractionalIdealAbsoluteNorm_prime]

/-- The norm of the principal fractional ideal `(x)` is the absolute field
norm of `x`. -/
theorem fractionalIdealAbsoluteNorm_toPrincipalIdeal (x : Kˣ) :
    ((fractionalIdealAbsoluteNorm
      (toPrincipalIdeal (𝓞 K) K x) : ℝ≥0ˣ) : ℝ≥0) =
      ⟨|((Algebra.norm ℚ) (x : K) : ℝ)|, abs_nonneg _⟩ := by
  apply NNReal.eq
  change
    ((FractionalIdeal.absNorm
      ((toPrincipalIdeal (𝓞 K) K x :
        (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) =
      |((Algebra.norm ℚ) (x : K) : ℝ)|
  rw [coe_toPrincipalIdeal,
    FractionalIdeal.absNorm_span_singleton, Rat.cast_abs]

end NumberField
