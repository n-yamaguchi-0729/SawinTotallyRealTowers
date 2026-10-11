/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.Integer

/-!
# Transport for subgroup value images

The common-top value-group comparison needs one transport step: the actual
ramification image is a subgroup of a larger common image, while the two lower
value-step inclusions are naturally proved for that larger common image.
-/

noncomputable section

namespace TameAbhyankar

open LocalFieldTheory.DiscreteValuationField

namespace MultiplicativeIntegerValuation

variable {G : Type _} [Group G]

/-- Lower value-step inclusions for a larger common image restrict to a
smaller ramification image and combine into the lcm value-step inclusion. -/
theorem subgroupValueSubgroup_le_integerMultipleSubgroup_lcm_of_le
    (V : MultiplicativeIntegerValuation G) {S T : Subgroup G} {d e : ℤ}
    (hST : S ≤ T)
    (hd : V.subgroupValueSubgroup T ≤ integerMultipleSubgroup d)
    (he : V.subgroupValueSubgroup T ≤ integerMultipleSubgroup e) :
    V.subgroupValueSubgroup S ≤
      integerMultipleSubgroup ((d.lcm e : ℕ) : ℤ) :=
  V.subgroupValueSubgroup_le_integerMultipleSubgroup_lcm S
    (V.subgroupValueSubgroup_le_integerMultipleSubgroup_of_le hST hd)
    (V.subgroupValueSubgroup_le_integerMultipleSubgroup_of_le hST he)

/-- Concrete transport form: if an actual element of the smaller ramification
image has valuation `n`, and the larger common image satisfies the two lower
value-step inclusions, then `n` is divisible by the lcm of the two lower
steps. -/
theorem int_lcm_dvd_of_exists_mem_val_of_le_of_subgroupValueSubgroup_le
    (V : MultiplicativeIntegerValuation G) {S T : Subgroup G} {n d e : ℤ}
    (hn : ∃ x : G, x ∈ S ∧ V.val x = n)
    (hST : S ≤ T)
    (hd : V.subgroupValueSubgroup T ≤ integerMultipleSubgroup d)
    (he : V.subgroupValueSubgroup T ≤ integerMultipleSubgroup e) :
    ((d.lcm e : ℕ) : ℤ) ∣ n :=
  V.int_lcm_dvd_of_exists_mem_val_of_subgroupValueSubgroup_le hn
    (V.subgroupValueSubgroup_le_integerMultipleSubgroup_of_le hST hd)
    (V.subgroupValueSubgroup_le_integerMultipleSubgroup_of_le hST he)

end MultiplicativeIntegerValuation

end TameAbhyankar

end
