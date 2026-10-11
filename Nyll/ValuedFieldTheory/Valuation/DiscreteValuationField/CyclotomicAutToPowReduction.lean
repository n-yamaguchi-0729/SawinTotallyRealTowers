/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Reduction of the action on primitive roots

The exponent of an automorphism on a primitive `p`-power root reduces to its
exponent on any primitive `p`-th root in the same field. The two roots need
not be chosen compatibly.
-/

namespace ValuationTheory.DiscreteValuationField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The finite cyclotomic action on a primitive `p^(s+1)`-th root reduces
to the action on any primitive `p`-th root. -/
theorem autToPow_unitsMap_prime_pow (p s : ℕ) [Fact p.Prime]
    {ζ η : L} (hζ : IsPrimitiveRoot ζ (p ^ (s + 1)))
    (hη : IsPrimitiveRoot η p) (σ : L ≃ₐ[K] L) :
    ZMod.unitsMap (dvd_pow_self p (Nat.succ_ne_zero s)) (hζ.autToPow K σ) =
      hη.autToPow K σ := by
  have hηpow : η ^ (p ^ (s + 1)) = 1 := by
    rw [pow_succ', pow_mul, hη.pow_eq_one, one_pow]
  obtain ⟨i, -, hpower⟩ := hζ.eq_pow_of_pow_eq_one hηpow
  have haction : η ^ (hζ.autToPow K σ : ZMod (p ^ (s + 1))).val = σ η := by
    rw [← hpower, ← pow_mul, Nat.mul_comm i, pow_mul,
      hζ.autToPow_spec K σ, map_pow]
  have heq :
      η ^ (hζ.autToPow K σ : ZMod (p ^ (s + 1))).val =
        η ^ (hη.autToPow K σ : ZMod p).val :=
    haction.trans (hη.autToPow_spec K σ).symm
  have hmod := (hη.isOfFinOrder (NeZero.ne p)).pow_eq_pow_iff_modEq.mp heq
  rw [← hη.eq_orderOf] at hmod
  apply Units.ext
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val]
  exact ((ZMod.natCast_eq_natCast_iff
    (hζ.autToPow K σ : ZMod (p ^ (s + 1))).val
    (hη.autToPow K σ : ZMod p).val p).mpr hmod).trans
      (ZMod.natCast_zmod_val (hη.autToPow K σ : ZMod p))

end ValuationTheory.DiscreteValuationField
