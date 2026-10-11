/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# A prime-power root obstruction in the Kummer quotient

A primitive `r`-th root cannot be an `r^s`-th power if the field has no
primitive `r^(s+1)`-th root.  The quotient here is the ordinary power-class
group used by `absoluteKummerContinuousNthRootsCharacterEquiv`.
-/

namespace KummerTheory

variable {K : Type*} [Field K]

/-- At the last available prime-power root level, a primitive root of prime
order has nonidentity power class.  The missing next root level is supplied
by maximality of `s` in the roots-downstairs argument. -/
theorem primitiveRoot_primePowerClass_ne_one
    {r : ℕ} (hr : r.Prime) (s : ℕ) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ r)
    (hnext : ¬ (primitiveRoots (r ^ (s + 1)) K).Nonempty) :
    (ζ : Kˣ ⧸ (powMonoidHom (r ^ s) : Kˣ →* Kˣ).range) ≠ 1 := by
  intro hclass
  obtain ⟨y, hy⟩ :=
    (QuotientGroup.eq_one_iff ζ).mp hclass
  change y ^ (r ^ s) = ζ at hy
  have hy_ne : y ^ (r ^ s) ≠ 1 := by
    rw [hy]
    exact hζ.ne_one hr.one_lt
  have hy_pow : y ^ (r ^ (s + 1)) = 1 := by
    rw [pow_succ, pow_mul, hy]
    exact hζ.pow_eq_one
  let : Fact r.Prime := ⟨hr⟩
  have hy_primitive : IsPrimitiveRoot y (r ^ (s + 1)) :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime_pow hy_ne hy_pow)
  exact hnext ⟨(y : K), (mem_primitiveRoots (pow_pos hr.pos (s + 1))).mpr
    (IsPrimitiveRoot.coe_units_iff.mpr hy_primitive)⟩

end KummerTheory
