/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.TopologyModelTypes

/-!
# Prime-power exponents without a finite residue field

Taking a residue-characteristic power moves a positive principal-unit level
one step deeper. Iteration kills `U^1 / U^(n+1)` by `p^n`, even when the
residue field and the level quotients are infinite.
-/

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

universe u v

variable {K : Type u} [Field K]
variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
variable (p : ℕ) [Fact p.Prime] [CharP F.residueField p]

/-- Iterating the prime-binomial containment moves `U^r` into `U^(r+n)`. -/
theorem pow_prime_pow_mem {r : ℕ} (hr : 1 ≤ r)
    {x : F.valuationSubringˣ} (hx : x ∈ higherPrincipalUnitGroup F r) (n : ℕ) :
    x ^ (p ^ n) ∈ higherPrincipalUnitGroup F (r + n) := by
  induction n with
  | zero => simpa only [pow_zero, pow_one, Nat.add_zero] using hx
  | succ n ih =>
    rw [pow_succ, pow_mul]
    exact pow_mem_succ_of_residue_ringChar_eq F (Fact.out : p.Prime)
      (hr.trans (Nat.le_add_right r n))
      ((ringChar.eq_iff (R := F.residueField)).2 inferInstance) ih

/-- The `n`-th principal-unit quotient is killed by `p^n`. -/
theorem Internal.principalUnitQuotientCarrier_pow_prime_pow_eq_one
    (n : ℕ) (x : Internal.principalUnitQuotientCarrier F n) :
    x ^ (p ^ n) = 1 := by
  rcases (toPrincipalUnitFiltration F).principalUnitSubquotientMk_surjective
      1 (n + 1) x with ⟨y, rfl⟩
  rw [← map_pow, (toPrincipalUnitFiltration F).principalUnitSubquotient_mk_eq_one_iff]
  change (y : F.valuationSubringˣ) ^ (p ^ n) ∈ higherPrincipalUnitGroup F (n + 1)
  simpa only [Nat.add_comm 1 n] using
    pow_prime_pow_mem F p (r := 1) (Nat.le_refl 1) y.property n

/-- The same exponent bound on the canonical discrete additive coordinate. -/
theorem DiscretePrincipalUnitQuotient.nsmul_prime_pow_eq_zero
    (n : ℕ) (x : DiscretePrincipalUnitQuotient F n) : (p ^ n) • x = 0 := by
  apply (DiscretePrincipalUnitQuotient.addEquiv F n).injective
  rw [map_nsmul, map_zero, DiscretePrincipalUnitQuotient.addEquiv_apply]
  change Additive.ofMul ((Additive.toMul x.val) ^ (p ^ n)) = Additive.ofMul 1
  rw [Internal.principalUnitQuotientCarrier_pow_prime_pow_eq_one F p]

end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
