/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Padic.TeichmullerReduction
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CyclotomicGaloisCard
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CyclotomicAutToPowReduction

/-!
# The p-adic character of a finite p-th cyclotomic extension

The action on the p-th roots of unity lifts by Teichmüller representatives
to p-adic units. It recovers the action on every p-power root present in
the extension, without assuming that all p-power roots are present.
-/

namespace LocalFieldTheory.DiscreteValuationField

open Examples.Qp
open ValuationTheory.DiscreteValuationField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} K L]

/-- The Teichmüller lift of the actual action on the `p`-th roots of unity. -/
noncomputable def primeCyclotomicTeichmullerCharacter : (L ≃ₐ[K] L) →* ℤ_[p]ˣ :=
  (teichmullerUnits p).comp ((IsCyclotomicExtension.zeta_spec p K L).autToPow K)

/-- The values of the finite cyclotomic character have order dividing `p - 1`. -/
theorem primeCyclotomicTeichmullerCharacter_pow (σ : L ≃ₐ[K] L) :
    primeCyclotomicTeichmullerCharacter K L p σ ^ (p - 1) = 1 :=
  teichmullerUnits_pow p ((IsCyclotomicExtension.zeta_spec p K L).autToPow K σ)

/-- At every positive prime-power level present in the field, the lifted
character agrees with the actual cyclotomic exponent. -/
theorem toZModPow_primeCyclotomicTeichmullerCharacter (s : ℕ)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (s + 1))) (σ : L ≃ₐ[K] L) :
    Units.map (PadicInt.toZModPow (s + 1)).toMonoidHom
      (primeCyclotomicTeichmullerCharacter K L p σ) = hζ.autToPow K σ := by
  have hσ : σ ^ (p - 1) = 1 := by
    obtain ⟨m, hm⟩ := cyclotomicGalois_natCard_dvd_prime_sub_one K L p
    rw [hm, pow_mul, pow_card_eq_one', one_pow]
  have hpower : hζ.autToPow K σ ^ (p - 1) = 1 := by
    rw [← map_pow, hσ, map_one]
  change Units.map (PadicInt.toZModPow (s + 1)).toMonoidHom
    (teichmullerUnits p ((IsCyclotomicExtension.zeta_spec p K L).autToPow K σ)) =
      hζ.autToPow K σ
  rw [← autToPow_unitsMap_prime_pow p s hζ (IsCyclotomicExtension.zeta_spec p K L) σ]
  exact toZModPow_teichmullerUnits_eq p s (hζ.autToPow K σ) hpower

/-- The lifted character gives the automorphism's action on every primitive
prime-power root contained in the extension. -/
theorem primeCyclotomicTeichmullerCharacter_spec (s : ℕ)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (s + 1))) (σ : L ≃ₐ[K] L) :
    ζ ^ (PadicInt.toZModPow (s + 1)
      (primeCyclotomicTeichmullerCharacter K L p σ : ℤ_[p])).val = σ ζ := by
  have h := congrArg (fun u : (ZMod (p ^ (s + 1)))ˣ => (u : ZMod (p ^ (s + 1))))
    (toZModPow_primeCyclotomicTeichmullerCharacter K L p s hζ σ)
  change PadicInt.toZModPow (s + 1)
    (primeCyclotomicTeichmullerCharacter K L p σ : ℤ_[p]) =
      (hζ.autToPow K σ : ZMod (p ^ (s + 1))) at h
  rw [h]
  exact hζ.autToPow_spec K σ

end LocalFieldTheory.DiscreteValuationField
