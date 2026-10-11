/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.PrimePowerExponent
import Mathlib.Algebra.Module.ZMod
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# P-adic scalars on principal-unit quotients with arbitrary residue field

The exponent `p^n` of the level quotient supplies its `ZMod (p^n)` module.
Reduction of p-adic integers then supplies the scalar action. These are
explicit constructions, avoiding competing local-field instances.
-/

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
namespace DiscretePrincipalUnitQuotient

universe u v

variable {K : Type u} [Field K]
variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
variable (p : ℕ) [Fact p.Prime] [CharP F.residueField p]

/-- Scalar reduction is justified by the actual prime-power exponent. -/
@[instance_reducible] noncomputable def zmodModule (n : ℕ) :
    Module (ZMod (p ^ n)) (DiscretePrincipalUnitQuotient F n) :=
  AddCommGroup.zmodModule (nsmul_prime_pow_eq_zero F p n)

/-- The level quotient as a p-adic module, without finiteness assumptions. -/
@[instance_reducible] noncomputable def padicModule (n : ℕ) :
    Module ℤ_[p] (DiscretePrincipalUnitQuotient F n) := by
  let : Module (ZMod (p ^ n)) (DiscretePrincipalUnitQuotient F n) := zmodModule F p n
  exact Module.compHom (DiscretePrincipalUnitQuotient F n) (PadicInt.toZModPow n)

/-- The action is given by an ordinary power representative modulo `p^n`. -/
theorem padic_smul_eq_val_nsmul (n : ℕ) (a : ℤ_[p])
    (x : DiscretePrincipalUnitQuotient F n) :
    (padicModule F p n).toSMul.smul a x = (PadicInt.toZModPow n a).val • x := by
  let : Module (ZMod (p ^ n)) (DiscretePrincipalUnitQuotient F n) := zmodModule F p n
  change PadicInt.toZModPow n a • x = (PadicInt.toZModPow n a).val • x
  rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), ZMod.natCast_zmod_val]

end DiscretePrincipalUnitQuotient
end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
