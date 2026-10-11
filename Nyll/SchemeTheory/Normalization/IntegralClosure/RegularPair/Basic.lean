/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.IntegralClosure.AwayPairIntersection
import Nyll.SchemeTheory.Normalization.IntegralClosure.RegularPair.TraceDual
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# A relatively-prime pair stays regular on a normalization

Let `A` be an integrally closed domain with fraction field `K`, let `L / K`
be algebraic, and let `B` be the integral closure of `A` in `L`.  If `x` is
prime and `x, y` are relatively prime nonzero elements of `A`, then the
equality `y * b = x * c` in `B` forces `x` to divide `b` in `B`.

The quotient `b / x` is integral over `A[1/x]`, while the equality identifies
it with `c / y`, which is integral over `A[1/y]`.  The two-localization
intersection theorem then puts the quotient back in the normalization.  No
global UFD instance is used.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped Pointwise

open nonZeroDivisors
open RingTheory.Sequence

universe u v w

/-- If `x` and `y` are relatively prime and `y * b = x * c` in the
normalization, then `b` is divisible by `x` in the normalization. -/
theorem exists_integralClosure_factor_of_mul_eq_mul
    {A : Type u} {K : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L]
    {x y : A} (hxPrime : Prime x) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : IsRelPrime x y)
    {b c : integralClosure A L}
    (hbc : algebraMap A (integralClosure A L) y * b =
      algebraMap A (integralClosure A L) x * c) :
    ∃ d : integralClosure A L,
      b = algebraMap A (integralClosure A L) x * d := by
  have hmap_ne_zero : ∀ {a : A}, a ≠ 0 → algebraMap A L a ≠ 0 := by
    intro a ha hazero
    rw [IsScalarTower.algebraMap_apply A K L] at hazero
    have hazeroK : algebraMap A K a = 0 := by
      apply (algebraMap K L).injective
      simpa using hazero
    apply ha
    apply IsFractionRing.injective A K
    simpa using hazeroK
  have hxL : algebraMap A L x ≠ 0 := hmap_ne_zero hx
  have hyL : algebraMap A L y ≠ 0 := hmap_ne_zero hy
  have hnotdvd : ¬ x ∣ y := by
    intro hdiv
    exact hxPrime.not_isUnit (hxy (dvd_refl x) hdiv)
  let z : L := (b : L) / algebraMap A L x
  have hz : IsIntegral A z := by
    apply isIntegral_of_isIntegral_localizationAway_pair_of_prime
      (K := K) hxPrime hy hnotdvd
    · let Aₓ := Localization.subalgebra.ofField K (Submonoid.powers x)
        (Submonoid.powers_le.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mpr hx))
      let : Algebra Aₓ L :=
        ((algebraMap K L).comp Aₓ.val).toAlgebra
      have hbase :
          (algebraMap Aₓ L).comp (algebraMap A Aₓ) =
            (RingHom.id L).comp (algebraMap A L) := by
        ext a
        change algebraMap K L (algebraMap A K a) = algebraMap A L a
        exact (IsScalarTower.algebraMap_apply A K L a).symm
      let xinv : Aₓ :=
        ⟨(algebraMap A K x)⁻¹, by
          change ∃ (a s : A) (_ : s ∈ Submonoid.powers x),
            (algebraMap A K x)⁻¹ =
              algebraMap A K a * (algebraMap A K s)⁻¹
          exact ⟨1, x, Submonoid.mem_powers x, by simp⟩⟩
      have hbInt : IsIntegral Aₓ (b : L) :=
        b.2.map_of_comp_eq (algebraMap A Aₓ) (RingHom.id L) hbase
      have hlocal : IsIntegral Aₓ
          (algebraMap Aₓ L xinv * (b : L)) :=
        isIntegral_algebraMap.mul hbInt
      have hxinvL : algebraMap Aₓ L xinv = (algebraMap A L x)⁻¹ := by
        change algebraMap K L ((algebraMap A K x)⁻¹) =
          (algebraMap A L x)⁻¹
        rw [map_inv₀, ← IsScalarTower.algebraMap_apply A K L]
      have hzx : z = algebraMap Aₓ L xinv * (b : L) := by
        rw [hxinvL]
        dsimp [z]
        simp [div_eq_mul_inv, mul_comm]
      rw [hzx]
      exact hlocal
    · let Aᵧ := Localization.subalgebra.ofField K (Submonoid.powers y)
        (Submonoid.powers_le.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mpr hy))
      let : Algebra Aᵧ L :=
        ((algebraMap K L).comp Aᵧ.val).toAlgebra
      have hbase :
          (algebraMap Aᵧ L).comp (algebraMap A Aᵧ) =
            (RingHom.id L).comp (algebraMap A L) := by
        ext a
        change algebraMap K L (algebraMap A K a) = algebraMap A L a
        exact (IsScalarTower.algebraMap_apply A K L a).symm
      let yinv : Aᵧ :=
        ⟨(algebraMap A K y)⁻¹, by
          change ∃ (a s : A) (_ : s ∈ Submonoid.powers y),
            (algebraMap A K y)⁻¹ =
              algebraMap A K a * (algebraMap A K s)⁻¹
          exact ⟨1, y, Submonoid.mem_powers y, by simp⟩⟩
      have hcInt : IsIntegral Aᵧ (c : L) :=
        c.2.map_of_comp_eq (algebraMap A Aᵧ) (RingHom.id L) hbase
      have hlocal : IsIntegral Aᵧ
          (algebraMap Aᵧ L yinv * (c : L)) :=
        isIntegral_algebraMap.mul hcInt
      have hyinvL : algebraMap Aᵧ L yinv = (algebraMap A L y)⁻¹ := by
        change algebraMap K L ((algebraMap A K y)⁻¹) =
          (algebraMap A L y)⁻¹
        rw [map_inv₀, ← IsScalarTower.algebraMap_apply A K L]
      have hzy : z = algebraMap Aᵧ L yinv * (c : L) := by
        rw [hyinvL]
        dsimp [z]
        rw [show (algebraMap A L y)⁻¹ * (c : L) =
          (c : L) / algebraMap A L y by
            simp [div_eq_mul_inv, mul_comm]]
        have hbcL : algebraMap A L y * (b : L) =
            algebraMap A L x * (c : L) := by
          exact congrArg Subtype.val hbc
        apply (div_eq_div_iff hxL hyL).2
        simpa [mul_comm] using hbcL
      rw [hzy]
      exact hlocal
  let d : integralClosure A L := ⟨z, hz⟩
  refine ⟨d, Subtype.ext ?_⟩
  change (b : L) = algebraMap A L x * z
  dsimp [z]
  rw [div_eq_mul_inv]
  symm
  calc
    algebraMap A L x * ((b : L) * (algebraMap A L x)⁻¹) =
        (b : L) * (algebraMap A L x * (algebraMap A L x)⁻¹) := by
          ac_rfl
    _ = (b : L) := by rw [mul_inv_cancel₀ hxL, mul_one]

/-- For a relatively-prime nonzero pair `x, y`, multiplication by `y` is
injective on the normalization modulo `x`.  This is the second regularity
condition needed for the parameter pair in the dimension-two flatness
argument. -/
theorem isSMulRegular_quotSMulTop_integralClosure_of_isRelPrime
    {A : Type u} {K : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L]
    {x y : A} (hxPrime : Prime x) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : IsRelPrime x y) :
    IsSMulRegular (QuotSMulTop x (integralClosure A L)) y := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro b hb
  rw [Submodule.mem_smul_pointwise_iff_exists] at hb ⊢
  obtain ⟨c, -, hcb⟩ := hb
  have hbc : algebraMap A (integralClosure A L) y * b =
      algebraMap A (integralClosure A L) x * c := by
    simpa only [Algebra.smul_def] using hcb.symm
  obtain ⟨d, hd⟩ :=
    exists_integralClosure_factor_of_mul_eq_mul
      (K := K) hxPrime hx hy hxy hbc
  refine ⟨d, Submodule.mem_top, ?_⟩
  simpa only [Algebra.smul_def] using hd.symm

/-- A regular pair remains regular in the second coordinate on a finite
normalization in a finite separable extension.

Unlike `isSMulRegular_quotSMulTop_integralClosure_of_isRelPrime`, this
finite-separable form needs neither integral closedness of the base nor a
primality hypothesis on the first parameter.  The trace-dual divisibility
theorem supplies precisely the saturation statement needed in the quotient.
-/
theorem isSMulRegular_quotSMulTop_integralClosure_of_isRegular
    {A : Type u} {K : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A (integralClosure A L)]
    {x y : A} (hregular : IsRegular A [x, y]) :
    IsSMulRegular (QuotSMulTop x (integralClosure A L)) y := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro b hb
  rw [Submodule.mem_smul_pointwise_iff_exists] at hb ⊢
  obtain ⟨c, -, hcb⟩ := hb
  have hbc : algebraMap A (integralClosure A L) y * b =
      algebraMap A (integralClosure A L) x * c := by
    simpa only [Algebra.smul_def] using hcb.symm
  obtain ⟨d, hd⟩ :=
    exists_integralClosure_factor_of_mul_eq_mul_of_isRegular
      (K := K) hregular hbc
  refine ⟨d, Submodule.mem_top, ?_⟩
  simpa only [Algebra.smul_def] using hd.symm

end EtaleFundamentalGroups
