/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.ProP.FrattiniPowers
import Mathlib.NumberTheory.NumberField.ClassNumber

set_option autoImplicit false
/-!
# The elementary `p`-class quotient

This file defines the ordinary ideal class group modulo `p`th powers and its
canonical dimension over `ZMod p` when `p` is prime.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet

open ClassFieldTower.ProP

variable (K : Type*) [Field K] [NumberField K]

/-- The subgroup of `p`th powers in the ordinary ideal class group. -/
def pClassPowerSubgroup (p : ℕ) : Subgroup (ClassGroup (𝓞 K)) :=
  powerSubgroup p (ClassGroup (𝓞 K))

local instance pClassPowerSubgroup_normal (p : ℕ) :
    (pClassPowerSubgroup K p).Normal := inferInstance

/-- The ordinary ideal class group modulo `p`th powers. -/
abbrev PClassGroup (p : ℕ) :=
  ClassGroup (𝓞 K) ⧸ pClassPowerSubgroup K p

omit [NumberField K] in
/-- Every element of the `p`-class quotient has exponent dividing `p`. -/
theorem pClassGroup_pow_eq_one (p : ℕ) (x : PClassGroup K p) :
    x ^ p = 1 := by
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (pClassPowerSubgroup K p) x
  rw [← map_pow]
  change ((g ^ p : ClassGroup (𝓞 K)) : PClassGroup K p) = 1
  rw [QuotientGroup.eq_one_iff]
  exact pow_mem_powerSubgroup p (ClassGroup (𝓞 K)) g

/-- The canonical `ZMod p`-dimension of the ordinary ideal class group modulo
`p`th powers. -/
noncomputable def pClassRank (p : ℕ) [Fact p.Prime] : ℕ := by
  letI : Module (ZMod p) (Additive (PClassGroup K p)) :=
    AddCommGroup.zmodModule (fun x => by
      change (Additive.toMul x) ^ p = 1
      exact pClassGroup_pow_eq_one K p (Additive.toMul x))
  exact Module.finrank (ZMod p) (Additive (PClassGroup K p))

/-- A multiplicative equivalence carries the power subgroup onto the power
subgroup. -/
theorem powerSubgroup_map_mulEquiv
    {G H : Type*} [Group G] [Group H] (p : ℕ) (e : G ≃* H) :
    (powerSubgroup p G).map e.toMonoidHom = powerSubgroup p H := by
  apply le_antisymm
  · exact powerSubgroup_map_le p G e.toMonoidHom
  · intro h hh
    have hrev :
        (powerSubgroup p H).map e.symm.toMonoidHom ≤ powerSubgroup p G :=
      powerSubgroup_map_le p H e.symm.toMonoidHom
    have hx : e.symm h ∈ powerSubgroup p G :=
      hrev ⟨h, hh, rfl⟩
    exact ⟨e.symm h, hx, e.apply_symm_apply h⟩

end ClassFieldTower.Martinet
