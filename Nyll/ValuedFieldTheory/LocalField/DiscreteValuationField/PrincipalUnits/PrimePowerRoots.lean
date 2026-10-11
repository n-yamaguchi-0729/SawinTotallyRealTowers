/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
import Nyll.ValuedFieldTheory.Valuation.PrincipalUnitRoots

/-!
# Field roots of principal units remain in the principal-unit group

A field element whose `p`-power is a principal unit is represented by an
actual element of the principal-unit subgroup, with the same power there.
This is the root used when taking logarithms of a Kummer relation.
-/

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

universe u v

variable {K : Type u} [Field K]

/-- A prime-power root in the field lifts to a root in the actual first
principal-unit group; its underlying field element is the prescribed root. -/
theorem exists_primePower_root_of_field_root
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    (p : ℕ) [Fact p.Prime] [hres : CharP F.residueField p]
    (s : ℕ) (y : K) (u : higherPrincipalUnitGroup F 1)
    (hy : y ^ (p ^ s) = (((u : F.valuationSubringˣ) : F.valuationSubring) : K)) :
    ∃ z : higherPrincipalUnitGroup F 1,
      (((z : F.valuationSubringˣ) : F.valuationSubring) : K) = y ∧
      z ^ (p ^ s) = u := by
  have humem := (mem_iff F 1 (u : F.valuationSubringˣ)).mp u.property
  rw [pow_one, F.mem_maximalIdeal_iff] at humem
  have hypow : F.valuation (y ^ (p ^ s) - 1) < 1 := by
    rw [hy]
    exact humem
  have hylt := (F.valuation.map_eq_one_and_sub_one_lt_one_of_prime_pow p s y hypow).2
  let a : F.valuationSubring := ⟨y - 1, hylt.le⟩
  have ha : a ∈ F.maximalIdeal ^ 1 := by
    rw [pow_one, F.mem_maximalIdeal_iff]
    exact hylt
  let z : higherPrincipalUnitGroup F 1 :=
    principalUnitOneAddOfMemPowSubgroup F (n := 1) le_rfl a ha
  have hz : (((z : F.valuationSubringˣ) : F.valuationSubring) : K) = y := by
    simp only [z, principalUnitOneAddOfMemPowSubgroup_val, principalUnitOneAddOfMemPow_val]
    change 1 + (y - 1) = y
    rw [← add_sub_assoc, add_sub_cancel_left]
  refine ⟨z, hz, ?_⟩
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  change ((((z : F.valuationSubringˣ) : F.valuationSubring) : K)) ^ (p ^ s) =
    (((u : F.valuationSubringˣ) : F.valuationSubring) : K)
  rw [hz]
  exact hy

end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
