/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Jacobson ideals under integral extension

An ideal contained in the Jacobson radical remains so after extension to an
integral algebra, because maximal ideals contract to maximal ideals.
-/

@[expose] public section

universe u v

namespace Ideal

/-- Extension to an integral algebra preserves containment in the Jacobson radical. -/
theorem map_le_jacobson_bot_of_isIntegral {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    {I : Ideal R} (hI : I ≤ jacobson ⊥) :
    I.map (algebraMap R S) ≤ jacobson ⊥ := by
  rw [jacobson, le_sInf_iff]
  rintro J ⟨_, hJ⟩
  let : J.IsMaximal := hJ
  apply map_le_iff_le_comap.mpr
  exact hI.trans (sInf_le ⟨bot_le,
    isMaximal_under_of_isIntegral_of_isMaximal (R := R) J⟩)

end Ideal
