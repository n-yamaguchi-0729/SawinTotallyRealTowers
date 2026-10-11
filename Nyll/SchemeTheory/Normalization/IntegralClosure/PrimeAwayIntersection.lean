/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Prime.Lemmas
import Mathlib.RingTheory.Localization.AsSubring

/-!
# Intersecting two principal localizations

Let `A` be a domain with fraction field `K`.  If `x` is prime and does not
divide the nonzero element `y`, then the images of `A[1/x]` and `A[1/y]`
inside `K` intersect in the image of `A`.

This is the small codimension-two intersection statement needed for the
normalization argument.  In particular, it avoids installing a global UFD
instance on `A`.
-/


noncomputable section

namespace EtaleFundamentalGroups

open nonZeroDivisors

universe u v

/-- If `x` is prime and `x ∤ y`, then a fraction lying in both `A[1/x]` and
`A[1/y]` already lies in `A`. -/
theorem mem_bot_of_mem_localizationAway_pair_of_prime
    {A : Type u} {K : Type v}
    [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {x y : A} (hx : Prime x) (hy : y ≠ 0) (hxy : ¬ x ∣ y)
    (z : K)
    (hzx : z ∈ Localization.subalgebra.ofField K (Submonoid.powers x)
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero)))
    (hzy : z ∈ Localization.subalgebra.ofField K (Submonoid.powers y)
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hy))) :
    z ∈ (⊥ : Subalgebra A K) := by
  change ∃ (a s : A) (_ : s ∈ Submonoid.powers x),
    z = algebraMap A K a * (algebraMap A K s)⁻¹ at hzx
  obtain ⟨a, sx, hsx, hzx⟩ := hzx
  obtain ⟨n, hsn⟩ := (Submonoid.mem_powers_iff sx x).mp hsx
  subst sx
  change ∃ (b s : A) (_ : s ∈ Submonoid.powers y),
    z = algebraMap A K b * (algebraMap A K s)⁻¹ at hzy
  obtain ⟨b, sy, hsy, hzy⟩ := hzy
  obtain ⟨m, hsm⟩ := (Submonoid.mem_powers_iff sy y).mp hsy
  subst sy
  have hxpowK : algebraMap A K (x ^ n) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr
      (pow_ne_zero n hx.ne_zero)
  have hypowK : algebraMap A K (y ^ m) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr
      (pow_ne_zero m hy)
  have hfrac :
      algebraMap A K a / algebraMap A K (x ^ n) =
        algebraMap A K b / algebraMap A K (y ^ m) := by
    calc
      algebraMap A K a / algebraMap A K (x ^ n) = z := by
        simpa only [div_eq_mul_inv] using hzx.symm
      _ = algebraMap A K b / algebraMap A K (y ^ m) := by
        simpa only [div_eq_mul_inv] using hzy
  have hcrossK :
      algebraMap A K a * algebraMap A K (y ^ m) =
        algebraMap A K b * algebraMap A K (x ^ n) :=
    (div_eq_div_iff hxpowK hypowK).mp hfrac
  have hcrossA : a * y ^ m = b * x ^ n := by
    apply IsFractionRing.injective A K
    simpa only [map_mul] using hcrossK
  have hpowdvd : x ^ n ∣ a * y ^ m := by
    refine ⟨b, ?_⟩
    simpa only [mul_comm] using hcrossA
  have hnotdvd : ¬ x ∣ y ^ m := fun h ↦ hxy (hx.dvd_of_dvd_pow h)
  obtain ⟨c, hac⟩ := hx.pow_dvd_of_dvd_mul_right n hnotdvd hpowdvd
  rw [Algebra.mem_bot]
  refine ⟨c, ?_⟩
  rw [hzx, hac, map_mul]
  calc
    algebraMap A K c = algebraMap A K c * 1 := by rw [mul_one]
    _ = algebraMap A K c *
        (algebraMap A K (x ^ n) * (algebraMap A K (x ^ n))⁻¹) := by
      rw [mul_inv_cancel₀ hxpowK]
    _ = (algebraMap A K (x ^ n) * algebraMap A K c) *
        (algebraMap A K (x ^ n))⁻¹ := by
      ac_rfl

end EtaleFundamentalGroups
