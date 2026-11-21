/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Field norms on unit groups

This file provides the common algebraic norm map on unit groups.  It is
independent of any valuation or local-field structure, so valued-field and
discrete-valuation APIs can share the same definition.
-/

@[expose] public section

namespace LocalFieldTheory

noncomputable section

universe u v w

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/-- Negation contributes one sign for each basis vector in the field norm. -/
theorem algebraNorm_neg (x : L) :
    Algebra.norm K (-x) = (-1) ^ Module.finrank K L * Algebra.norm K x := by
  rw [show -x = algebraMap K L (-1) * x by rw [map_neg, map_one, neg_one_mul],
    map_mul, Algebra.norm_algebraMap]

/-- The algebra norm, restricted to unit groups. -/
def normUnits : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

/-- The underlying field element of a unit norm is the algebra norm. -/
@[simp]
theorem normUnits_apply_coe (x : Lˣ) :
    ((normUnits K L x : Kˣ) : K) = Algebra.norm K (x : L) :=
  rfl

/-- The image of the field norm on unit groups. -/
def localNormSubgroup : Subgroup Kˣ :=
  (normUnits K L).range

/-- Field norms on unit groups are transitive in a tower. -/
theorem normUnits_tower
    (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [Module.Free M L] (x : Lˣ) :
    normUnits K M (normUnits M L x) = normUnits K L x := by
  apply Units.ext
  exact Algebra.norm_norm

/-- A norm down a tower already lies in the norm subgroup of each intermediate field. -/
theorem localNormSubgroup_le_of_tower
    (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [Module.Free M L] :
    localNormSubgroup K L ≤ localNormSubgroup K M := by
  rintro x ⟨y, rfl⟩
  exact ⟨normUnits M L y, normUnits_tower K M L y⟩

end

end LocalFieldTheory
