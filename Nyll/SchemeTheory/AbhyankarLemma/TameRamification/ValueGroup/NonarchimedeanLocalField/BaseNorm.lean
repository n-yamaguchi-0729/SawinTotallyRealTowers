/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Invariants

/-!
# Norms of base units in Neu1999 local fields

This file supplies concrete elements of field-norm subgroups coming from base
units.  It is an element-level source for later ramification-image comparisons.
-/

noncomputable section

universe u

namespace TameAbhyankar

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField

namespace NAField

variable {K L : Type u}
variable [Field K] [Field L] [Algebra K L]

/-- The field norm of a base unit embedded into the extension is the
`[L : K]`-th power of that base unit. -/
theorem fieldNormUnits_mapBaseUnitsToExtensionUnits
    (x : Kˣ) :
    normUnits K L
        (LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits K L x) =
      x ^ Module.finrank K L := by
  ext
  simp [normUnits, LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits,
    Algebra.norm_algebraMap]

/-- Every `[L : K]`-th power of a base unit lies in the field-norm subgroup
from `L/K`. -/
theorem pow_finrank_mem_fieldNormSubgroup (x : Kˣ) :
    x ^ Module.finrank K L ∈ fieldNormSubgroup K L := by
  rw [← fieldNormUnits_mapBaseUnitsToExtensionUnits (K := K) (L := L) x]
  exact
    ⟨LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits
      K L x, rfl⟩

section Valuation

variable [ValuativeRel K] [TopologicalSpace K]
variable [IsNonarchimedeanLocalField K]

/-- A base uniformizer gives a concrete field-norm subgroup element whose
valuation is the field degree `[L : K]`. -/
theorem exists_mem_fieldNormSubgroup_val_finrank_of_uniformizer
    {ϖ : Kˣ} (hϖ : (multiplicativeIntegerValuation K).IsUniformizer ϖ) :
    ∃ x : Kˣ, x ∈ fieldNormSubgroup K L ∧
      (multiplicativeIntegerValuation K).val x =
        (Module.finrank K L : ℤ) := by
  refine ⟨ϖ ^ Module.finrank K L,
    pow_finrank_mem_fieldNormSubgroup (K := K) (L := L) ϖ, ?_⟩
  calc
    (multiplicativeIntegerValuation K).val
        (ϖ ^ Module.finrank K L) =
        (multiplicativeIntegerValuation K).val
          (ϖ ^ (Module.finrank K L : ℤ)) := by
      simp
    _ = (Module.finrank K L : ℤ) := by
      rw [(multiplicativeIntegerValuation K).val_zpow, hϖ, mul_one]

/-- A Neu1999 base local field supplies a concrete field-norm subgroup element
whose valuation is the field degree `[L : K]`. -/
theorem exists_mem_fieldNormSubgroup_val_finrank :
    ∃ x : Kˣ, x ∈ fieldNormSubgroup K L ∧
      (multiplicativeIntegerValuation K).val x =
        (Module.finrank K L : ℤ) := by
  rcases multiplicativeIntegerValuation_exists_uniformizer K with ⟨ϖ, hϖ⟩
  exact exists_mem_fieldNormSubgroup_val_finrank_of_uniformizer
    (K := K) (L := L) hϖ

end Valuation

end NAField

end TameAbhyankar

end
