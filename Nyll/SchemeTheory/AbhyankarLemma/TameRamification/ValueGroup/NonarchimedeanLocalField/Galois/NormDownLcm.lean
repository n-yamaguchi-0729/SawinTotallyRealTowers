/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Galois.NormDown

/-!
# Galois norm-down lcm value-step inclusions

This file keeps the Galois residue-degree lcm subgroup comparisons for the
norm-down ramification image separate from the construction of that image.
-/

noncomputable section

universe u

namespace TameAbhyankar

open LocalFieldTheory.DiscreteValuationField
open scoped ValuativeRel

namespace NAField

section GaloisNormPoweredLcm

variable {K L L' M : Type u}
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
variable [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L]
variable [IsNonarchimedeanLocalField L]
variable [Field L'] [ValuativeRel L'] [TopologicalSpace L']
variable [IsNonarchimedeanLocalField L']
variable [Field M]
variable [Algebra K L] [Algebra K L']
variable [Algebra K M]
variable [Algebra L M] [Algebra L' M]
variable [IsScalarTower K L M] [IsScalarTower K L' M]
variable [Module.Free L M] [Module.Free L' M]
variable [FiniteDimensional K L] [IsGalois K L]
variable [FiniteDimensional K L'] [IsGalois K L']
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L')]

/-- The concrete normed powered ramification image inherits the common-top
Galois residue-degree lcm value-step inclusion. -/
theorem normPoweredBaseUnitsImageSubgroup_valueImage_le_galoisResidueDegree_lcm :
    (multiplicativeIntegerValuation K).subgroupValueSubgroup
        (normPoweredBaseUnitsImageSubgroup (K := K) (L := L) (M := M)) ≤
      integerMultipleSubgroup
        ((((Module.finrank 𝓀[K] 𝓀[L] : ℤ).lcm
          (Module.finrank 𝓀[K] 𝓀[L'] : ℤ) : ℕ) : ℤ)) :=
  subgroupValueSubgroup_le_galoisResidueDegree_lcm_of_le_fieldNormSubgroup
    (K := K) (L := L) (L' := L') (M := M)
    (S := normPoweredBaseUnitsImageSubgroup (K := K) (L := L) (M := M))
    (normPoweredBaseUnitsImageSubgroup_le_fieldNormSubgroup_top
      (K := K) (L := L) (M := M))

/-- Symmetric branch version of the concrete normed powered ramification-image
Galois residue-degree lcm value-step inclusion. -/
theorem normPoweredBaseUnitsImageSubgroup_valueImage_le_galoisResidueDegree_lcm_symm :
    (multiplicativeIntegerValuation K).subgroupValueSubgroup
        (normPoweredBaseUnitsImageSubgroup (K := K) (L := L') (M := M)) ≤
      integerMultipleSubgroup
        ((((Module.finrank 𝓀[K] 𝓀[L'] : ℤ).lcm
          (Module.finrank 𝓀[K] 𝓀[L] : ℤ) : ℕ) : ℤ)) := by
  simpa using
    normPoweredBaseUnitsImageSubgroup_valueImage_le_galoisResidueDegree_lcm
      (K := K) (L := L') (L' := L) (M := M)

end GaloisNormPoweredLcm

section GaloisNormDownLcmSubgroup

variable {K L L' M : Type u}
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
variable [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L]
variable [IsNonarchimedeanLocalField L]
variable [Field L'] [ValuativeRel L'] [TopologicalSpace L']
variable [IsNonarchimedeanLocalField L']
variable [Field M]
variable [Algebra K L] [Algebra K L']
variable [Algebra K M]
variable [Algebra L M] [Algebra L' M]
variable [IsScalarTower K L M] [IsScalarTower K L' M]
variable [Module.Free L M] [Module.Free L' M]
variable [FiniteDimensional K L] [IsGalois K L]
variable [FiniteDimensional K L'] [IsGalois K L']
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L')]

/-- Subgroup-value form of the lcm divisor carried by the Galois norm-down
ramification step. -/
theorem integerMultipleSubgroup_galoisNormDownRamificationStep_le_lcm :
    integerMultipleSubgroup
        (galoisNormDownRamificationStepNat (K := K) (L := L) (M := M) :
          ℤ) ≤
      integerMultipleSubgroup
        ((((Module.finrank 𝓀[K] 𝓀[L] : ℤ).lcm
          (Module.finrank 𝓀[K] 𝓀[L'] : ℤ) : ℕ) : ℤ)) := by
  rw [← normPoweredBaseUnitsImageSubgroup_valueImage_eq_galoisNormDownRamificationStep
    (K := K) (L := L) (M := M)]
  exact
    normPoweredBaseUnitsImageSubgroup_valueImage_le_galoisResidueDegree_lcm
      (K := K) (L := L) (L' := L') (M := M)

end GaloisNormDownLcmSubgroup

section GaloisNormDownLcmSubgroupSymm

variable {K L L' M : Type u}
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
variable [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L]
variable [IsNonarchimedeanLocalField L]
variable [Field L'] [ValuativeRel L'] [TopologicalSpace L']
variable [IsNonarchimedeanLocalField L']
variable [Field M]
variable [Algebra K L] [Algebra K L']
variable [Algebra K M]
variable [Algebra L M] [Algebra L' M]
variable [IsScalarTower K L M] [IsScalarTower K L' M]
variable [Module.Free L M] [Module.Free L' M]
variable [FiniteDimensional K L] [IsGalois K L]
variable [FiniteDimensional K L'] [IsGalois K L']
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L')]

/-- Symmetric subgroup-value form of the lcm divisor carried by the Galois
norm-down ramification step. -/
theorem integerMultipleSubgroup_galoisNormDownRamificationStep_le_lcm_symm :
    integerMultipleSubgroup
        (galoisNormDownRamificationStepNat (K := K) (L := L') (M := M) :
          ℤ) ≤
      integerMultipleSubgroup
        ((((Module.finrank 𝓀[K] 𝓀[L'] : ℤ).lcm
          (Module.finrank 𝓀[K] 𝓀[L] : ℤ) : ℕ) : ℤ)) := by
  simpa using
    integerMultipleSubgroup_galoisNormDownRamificationStep_le_lcm
      (K := K) (L := L') (L' := L) (M := M)

end GaloisNormDownLcmSubgroupSymm

end NAField

end TameAbhyankar

end
