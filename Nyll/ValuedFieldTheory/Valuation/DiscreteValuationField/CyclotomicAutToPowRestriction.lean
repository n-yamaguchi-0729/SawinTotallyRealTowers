/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Cyclotomic exponents under restriction

Restricting an automorphism along two field towers preserves its exponent
on primitive roots. The primitive roots in the two fields may be chosen
independently; neither bijectivity of restriction nor a compositum
hypothesis is needed.
-/

namespace ValuationTheory.DiscreteValuationField

variable {F K L E : Type*} [Field F] [Field K] [Field L] [Field E]
  [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K E] [Algebra L E]
  [IsScalarTower F K E] [IsScalarTower F L E] [Normal F K]

private theorem restrictRestrict_algebraMap (σ : E ≃ₐ[L] E) (x : K) :
    algebraMap K E (IntermediateField.restrictRestrictAlgEquivMapHom F K L E σ x) =
      σ (algebraMap K E x) :=
  (MulSemiringAction.toAlgAut (E ≃ₐ[L] E) F E σ).restrictNormal_commutes K x

/-- The actual restriction homomorphism preserves the cyclotomic exponent,
independently of the primitive roots chosen in the two fields. -/
theorem autToPow_restrictRestrictAlgEquivMapHom (n : ℕ) [NeZero n]
    {ζ : K} {η : E} (hζ : IsPrimitiveRoot ζ n) (hη : IsPrimitiveRoot η n)
    (σ : E ≃ₐ[L] E) :
    hζ.autToPow F (IntermediateField.restrictRestrictAlgEquivMapHom F K L E σ) =
      hη.autToPow L σ := by
  have hroot : (algebraMap K E ζ) ^ n = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨i, -, himage⟩ := hη.eq_pow_of_pow_eq_one hroot
  have haction : (algebraMap K E ζ) ^ (hη.autToPow L σ : ZMod n).val =
      σ (algebraMap K E ζ) := by
    rw [← himage, ← pow_mul, Nat.mul_comm i, pow_mul,
      hη.autToPow_spec L σ, map_pow]
  apply Units.ext
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  apply (algebraMap K E).injective
  rw [hζ.autToPow_spec F (IntermediateField.restrictRestrictAlgEquivMapHom F K L E σ),
    restrictRestrict_algebraMap, map_pow]
  exact haction.symm

end ValuationTheory.DiscreteValuationField
