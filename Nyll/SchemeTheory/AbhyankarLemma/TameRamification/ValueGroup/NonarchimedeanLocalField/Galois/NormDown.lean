/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Index
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.GaloisInvariants
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Galois.Ramification.Basic
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Galois.Ramification.ValueImage
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Galois.Ramification.LocalTop

/-!
# Normed Galois ramification images

This file studies the image obtained by applying `N_{L/K}` to the powered
embedded-base-unit ramification image.  It keeps the common-top norm containment
and its valuation generator in a separate source layer.
-/

noncomputable section

universe u

namespace TameAbhyankar

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open scoped ValuativeRel

namespace NAField

section NormDownValue

variable {K L M : Type u}
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
variable [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L]
variable [IsNonarchimedeanLocalField L]
variable [Field M]
variable [Algebra K L] [Algebra L M]
variable [FiniteDimensional K L] [IsGalois K L]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]

/-- The base valuation step generated after applying `N_{L/K}` to the powered
embedded-base-unit ramification image from `L`. -/
def normDownRamificationStepNat : ℕ :=
  Module.finrank 𝓀[K] 𝓀[L] *
    (Module.finrank L M *
      Ideal.ramificationIdx (𝓂[L] : Ideal 𝒪[L]) 𝒪[K])

/-- The normed powered embedded-base-unit subgroup contains an element whose
base valuation is the norm-down ramification step. -/
theorem exists_mem_normPoweredBaseUnitsImageSubgroup_val_normDownRamificationStep :
    ∃ x : Kˣ,
      x ∈ normPoweredBaseUnitsImageSubgroup (K := K) (L := L) (M := M) ∧
        (multiplicativeIntegerValuation K).val x =
          (normDownRamificationStepNat (K := K) (L := L) (M := M) : ℤ) := by
  rcases exists_mem_poweredBaseUnitsImageSubgroup_val_finrank_mul_galoisRamificationIndex
      (K := K) (L := L) (M := M) with
    ⟨y, hyS, hyval⟩
  refine ⟨normUnits K L y, ⟨y, hyS, rfl⟩, ?_⟩
  rw [fieldNormUnits_valuation_formula (K := K) (L := L) y, hyval]
  simp [normDownRamificationStepNat, Nat.cast_mul]

/-- The norm-down ramification step generates values inside the normed powered
embedded-base-unit subgroup. -/
theorem integerMultipleSubgroup_normDownRamificationStep_le_normPowered :
    integerMultipleSubgroup
        (normDownRamificationStepNat (K := K) (L := L) (M := M) : ℤ) ≤
      (multiplicativeIntegerValuation K).subgroupValueSubgroup
        (normPoweredBaseUnitsImageSubgroup (K := K) (L := L) (M := M)) :=
  MultiplicativeIntegerValuation.integerMultipleSubgroup_le_subgroupValueSubgroup_of_exists_mem_val
    (multiplicativeIntegerValuation K)
    (exists_mem_normPoweredBaseUnitsImageSubgroup_val_normDownRamificationStep
      (K := K) (L := L) (M := M))

/-- Every value appearing in the normed powered embedded-base-unit subgroup is
a multiple of the norm-down ramification step. -/
theorem normPoweredBaseUnitsImageSubgroup_valueImage_le_normDownRamificationStep :
    (multiplicativeIntegerValuation K).subgroupValueSubgroup
        (normPoweredBaseUnitsImageSubgroup (K := K) (L := L) (M := M)) ≤
      integerMultipleSubgroup
        (normDownRamificationStepNat (K := K) (L := L) (M := M) : ℤ) := by
  exact
    (MultiplicativeIntegerValuation.subgroupValueSubgroup_le_integerMultipleSubgroup_iff
      (multiplicativeIntegerValuation K)
      (normPoweredBaseUnitsImageSubgroup (K := K) (L := L) (M := M))
      (normDownRamificationStepNat (K := K) (L := L) (M := M) : ℤ)).2
      (fun x hx => by
        rcases hx with ⟨y, hyS, hyx⟩
        have hydiv :
            ((Module.finrank L M *
              Ideal.ramificationIdx (𝓂[L] : Ideal 𝒪[L]) 𝒪[K] : ℕ) : ℤ) ∣
              (multiplicativeIntegerValuation L).val y := by
          have hraw :
              ((Module.finrank L M : ℤ) *
                (Ideal.ramificationIdx (𝓂[L] : Ideal 𝒪[L]) 𝒪[K] : ℤ)) ∣
                (multiplicativeIntegerValuation L).val y :=
            (MultiplicativeIntegerValuation.subgroupValueSubgroup_le_integerMultipleSubgroup_iff
              (multiplicativeIntegerValuation L)
              (poweredBaseUnitsImageSubgroup (K := K) (L := L) (M := M))
              ((Module.finrank L M : ℤ) *
                (Ideal.ramificationIdx (𝓂[L] : Ideal 𝒪[L]) 𝒪[K] : ℤ))).1
              (poweredBaseUnitsImageSubgroup_valueImage_le_finrank_mul_galoisRamificationIndex
                (K := K) (L := L) (M := M)) y hyS
          simpa [Nat.cast_mul] using hraw
        rw [← hyx]
        change
          (normDownRamificationStepNat (K := K) (L := L) (M := M) : ℤ) ∣
            (multiplicativeIntegerValuation K).val (normUnits K L y)
        rw [fieldNormUnits_valuation_formula (K := K) (L := L) y]
        simpa [normDownRamificationStepNat, Nat.cast_mul, mul_assoc] using
          mul_dvd_mul_left
            (Module.finrank 𝓀[K] 𝓀[L] : ℤ) hydiv)

/-- Exact value image of the normed powered embedded-base-unit subgroup. -/
theorem normPoweredBaseUnitsImageSubgroup_valueImage_eq_normDownRamificationStep :
    (multiplicativeIntegerValuation K).subgroupValueSubgroup
        (normPoweredBaseUnitsImageSubgroup (K := K) (L := L) (M := M)) =
      integerMultipleSubgroup
        (normDownRamificationStepNat (K := K) (L := L) (M := M) : ℤ) :=
  le_antisymm
    (normPoweredBaseUnitsImageSubgroup_valueImage_le_normDownRamificationStep
      (K := K) (L := L) (M := M))
    (integerMultipleSubgroup_normDownRamificationStep_le_normPowered
      (K := K) (L := L) (M := M))

end NormDownValue

section GaloisNormDownValue

variable {K L M : Type u}
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
variable [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L]
variable [IsNonarchimedeanLocalField L]
variable [Field M]
variable [Algebra K L] [Algebra L M]
variable [FiniteDimensional K L] [IsGalois K L]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]

/-- Galois-data form of the normed powered embedded-base-unit generator. -/
theorem exists_mem_normPoweredBaseUnitsImageSubgroup_val_galoisNormDownRamificationStep :
    ∃ x : Kˣ,
      x ∈ normPoweredBaseUnitsImageSubgroup (K := K) (L := L) (M := M) ∧
        (multiplicativeIntegerValuation K).val x =
          (galoisNormDownRamificationStepNat (K := K) (L := L) (M := M) :
            ℤ) := by
  simpa [normDownRamificationStepNat, galoisNormDownRamificationStepNat] using
    exists_mem_normPoweredBaseUnitsImageSubgroup_val_normDownRamificationStep
      (K := K) (L := L) (M := M)

/-- The Galois norm-down step generates values in the normed powered
embedded-base-unit subgroup. -/
theorem integerMultipleSubgroup_galoisNormDownRamificationStep_le_normPowered :
    integerMultipleSubgroup
        (galoisNormDownRamificationStepNat (K := K) (L := L) (M := M) :
          ℤ) ≤
      (multiplicativeIntegerValuation K).subgroupValueSubgroup
        (normPoweredBaseUnitsImageSubgroup (K := K) (L := L) (M := M)) :=
  MultiplicativeIntegerValuation.integerMultipleSubgroup_le_subgroupValueSubgroup_of_exists_mem_val
    (multiplicativeIntegerValuation K)
    (exists_mem_normPoweredBaseUnitsImageSubgroup_val_galoisNormDownRamificationStep
      (K := K) (L := L) (M := M))

/-- Every value in the normed powered subgroup is a multiple of the Galois
norm-down ramification step. -/
theorem normPoweredBaseUnitsImageSubgroup_valueImage_le_galoisNormDownRamificationStep :
    (multiplicativeIntegerValuation K).subgroupValueSubgroup
        (normPoweredBaseUnitsImageSubgroup (K := K) (L := L) (M := M)) ≤
      integerMultipleSubgroup
        (galoisNormDownRamificationStepNat (K := K) (L := L) (M := M) :
          ℤ) := by
  simpa [normDownRamificationStepNat, galoisNormDownRamificationStepNat] using
    normPoweredBaseUnitsImageSubgroup_valueImage_le_normDownRamificationStep
      (K := K) (L := L) (M := M)

/-- Exact Galois-data value image of the normed powered embedded-base-unit
subgroup. -/
theorem normPoweredBaseUnitsImageSubgroup_valueImage_eq_galoisNormDownRamificationStep :
    (multiplicativeIntegerValuation K).subgroupValueSubgroup
        (normPoweredBaseUnitsImageSubgroup (K := K) (L := L) (M := M)) =
      integerMultipleSubgroup
        (galoisNormDownRamificationStepNat (K := K) (L := L) (M := M) :
          ℤ) :=
  le_antisymm
    (normPoweredBaseUnitsImageSubgroup_valueImage_le_galoisNormDownRamificationStep
      (K := K) (L := L) (M := M))
    (integerMultipleSubgroup_galoisNormDownRamificationStep_le_normPowered
      (K := K) (L := L) (M := M))

end GaloisNormDownValue

section CommonTopNormDownGenerator

variable {K L M : Type u}
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
variable [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L]
variable [IsNonarchimedeanLocalField L]
variable [Field M]
variable [Algebra K L] [Algebra K M] [Algebra L M]
variable [IsScalarTower K L M] [Module.Free L M]
variable [FiniteDimensional K L] [IsGalois K L]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]

/-- The common-top field-norm subgroup contains the concrete norm-down
ramification-image generator. -/
theorem exists_mem_fieldNormSubgroup_val_normDownRamificationStep :
    ∃ x : Kˣ,
      x ∈ fieldNormSubgroup K M ∧
        (multiplicativeIntegerValuation K).val x =
          (normDownRamificationStepNat (K := K) (L := L) (M := M) : ℤ) := by
  rcases exists_mem_normPoweredBaseUnitsImageSubgroup_val_normDownRamificationStep
      (K := K) (L := L) (M := M) with
    ⟨x, hxS, hxval⟩
  exact ⟨x,
    normPoweredBaseUnitsImageSubgroup_le_fieldNormSubgroup_top
      (K := K) (L := L) (M := M) hxS,
    hxval⟩

/-- Subgroup-value form of the common-top raw norm-down generator. -/
theorem integerMultipleSubgroup_normDownRamificationStep_le_fieldNormSubgroup :
    integerMultipleSubgroup
        (normDownRamificationStepNat (K := K) (L := L) (M := M) : ℤ) ≤
      (multiplicativeIntegerValuation K).subgroupValueSubgroup
        (fieldNormSubgroup K M) :=
  MultiplicativeIntegerValuation.integerMultipleSubgroup_le_subgroupValueSubgroup_of_exists_mem_val
    (multiplicativeIntegerValuation K)
    (exists_mem_fieldNormSubgroup_val_normDownRamificationStep
      (K := K) (L := L) (M := M))

end CommonTopNormDownGenerator

section GaloisCommonTopNormDownGenerator

variable {K L M : Type u}
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
variable [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L]
variable [IsNonarchimedeanLocalField L]
variable [Field M]
variable [Algebra K L] [Algebra K M] [Algebra L M]
variable [IsScalarTower K L M] [Module.Free L M]
variable [FiniteDimensional K L] [IsGalois K L]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]

/-- Galois-data form of the concrete common-top norm-down generator. -/
theorem exists_mem_fieldNormSubgroup_val_galoisNormDownRamificationStep :
    ∃ x : Kˣ,
      x ∈ fieldNormSubgroup K M ∧
        (multiplicativeIntegerValuation K).val x =
          (galoisNormDownRamificationStepNat (K := K) (L := L) (M := M) :
            ℤ) := by
  simpa [normDownRamificationStepNat, galoisNormDownRamificationStepNat] using
    exists_mem_fieldNormSubgroup_val_normDownRamificationStep
      (K := K) (L := L) (M := M)

/-- Subgroup-value form of the common-top Galois norm-down generator. -/
theorem integerMultipleSubgroup_galoisNormDownRamificationStep_le_fieldNormSubgroup :
    integerMultipleSubgroup
        (galoisNormDownRamificationStepNat (K := K) (L := L) (M := M) :
          ℤ) ≤
      (multiplicativeIntegerValuation K).subgroupValueSubgroup
        (fieldNormSubgroup K M) :=
  MultiplicativeIntegerValuation.integerMultipleSubgroup_le_subgroupValueSubgroup_of_exists_mem_val
    (multiplicativeIntegerValuation K)
    (exists_mem_fieldNormSubgroup_val_galoisNormDownRamificationStep
      (K := K) (L := L) (M := M))

end GaloisCommonTopNormDownGenerator

section CommonTop

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
variable [FiniteDimensional K L'] [Algebra.IsSeparable K L']
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L')]

/-- Common-top norm containment forces the lower residue-degree lcm to divide
the norm-down Galois ramification step. -/
theorem nat_lcm_residueDegree_dvd_normDownRamificationStep :
    Nat.lcm (Module.finrank 𝓀[K] 𝓀[L])
        (Module.finrank 𝓀[K] 𝓀[L']) ∣
      normDownRamificationStepNat (K := K) (L := L) (M := M) :=
  nat_lcm_residueDegree_dvd_nat_of_exists_mem_val_of_le_fieldNormSubgroup_towers
    (K := K) (L := L) (L' := L') (M := M)
    (S := normPoweredBaseUnitsImageSubgroup (K := K) (L := L) (M := M))
    (n := normDownRamificationStepNat (K := K) (L := L) (M := M))
    (exists_mem_normPoweredBaseUnitsImageSubgroup_val_normDownRamificationStep
      (K := K) (L := L) (M := M))
    (normPoweredBaseUnitsImageSubgroup_le_fieldNormSubgroup_top
      (K := K) (L := L) (M := M))

end CommonTop

section GaloisNormDownLcm

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

/-- The concrete norm-down ramification-image generator already carries the
lcm of the two lower Galois residue degrees. -/
theorem nat_lcm_galoisResidueDegree_dvd_galoisNormDownRamificationStep :
    Nat.lcm
        (Module.finrank 𝓀[K] 𝓀[L])
        (Module.finrank 𝓀[K] 𝓀[L']) ∣
      galoisNormDownRamificationStepNat (K := K) (L := L) (M := M) := by
  exact nat_lcm_galoisResidueDegree_dvd_nat_of_mem_le_fieldNormSubgroup
    (K := K) (L := L) (L' := L') (M := M)
    (S := fieldNormSubgroup K M)
    (n := galoisNormDownRamificationStepNat (K := K) (L := L) (M := M))
    (exists_mem_fieldNormSubgroup_val_galoisNormDownRamificationStep
      (K := K) (L := L) (M := M))
    (fun _ hx => hx)

end GaloisNormDownLcm

section CanonicalGaloisInvariants

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
variable [FiniteDimensional K L] [FiniteDimensional L M]
variable [IsGalois K L]
variable [FiniteDimensional K L'] [Algebra.IsSeparable K L']
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L')]

/-- With the lower `L/K` invariants supplied by Galois valuation data, the
norm-down value-image lcm comparison becomes a field-degree divisibility. -/
theorem nat_lcm_galoisResidueDegree_dvd_finrank :
    Nat.lcm
        (Module.finrank 𝓀[K] 𝓀[L])
        (Module.finrank 𝓀[K] 𝓀[L']) ∣
      Module.finrank K M := by
  have hdiv :=
    nat_lcm_residueDegree_dvd_normDownRamificationStep
      (K := K) (L := L) (L' := L') (M := M)
  have hstep :
      normDownRamificationStepNat (K := K) (L := L) (M := M) =
        Module.finrank K M := by
    change
      galoisNormDownRamificationStepNat (K := K) (L := L) (M := M) =
        Module.finrank K M
    exact galoisNormDownRamificationStepNat_eq_finrank
      (K := K) (L := L) (M := M)
  simpa [hstep] using hdiv

end CanonicalGaloisInvariants

section CanonicalGaloisInvariantsBoth

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
variable [FiniteDimensional K L] [FiniteDimensional L M]
variable [IsGalois K L]
variable [FiniteDimensional K L'] [IsGalois K L']
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L')]

/-- If both lower branches are supplied by Neu1999 Galois valuation data, the
common-top norm-down comparison gives a top-degree divisibility by the lcm of
the two Galois residue degrees. -/
theorem nat_lcm_galoisResidueDegree_dvd_finrank_both :
    Nat.lcm
        (Module.finrank 𝓀[K] 𝓀[L])
        (Module.finrank 𝓀[K] 𝓀[L']) ∣
      Module.finrank K M := by
  have hstep :
      galoisNormDownRamificationStepNat (K := K) (L := L) (M := M) =
        Module.finrank K M :=
    galoisNormDownRamificationStepNat_eq_finrank
      (K := K) (L := L) (M := M)
  simpa [hstep] using
    nat_lcm_galoisResidueDegree_dvd_galoisNormDownRamificationStep
      (K := K) (L := L) (L' := L') (M := M)

end CanonicalGaloisInvariantsBoth

section CanonicalGaloisInvariantsSymm

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
variable [FiniteDimensional K L'] [FiniteDimensional L' M]
variable [IsGalois K L']
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L')]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]

/-- Symmetric field-degree form with the `L'/K` invariants supplied by Galois
valuation data. -/
theorem nat_lcm_galoisResidueDegree_dvd_finrank_symm :
    Nat.lcm
        (Module.finrank 𝓀[K] 𝓀[L'])
        (Module.finrank 𝓀[K] 𝓀[L]) ∣
      Module.finrank K M := by
  have hdiv :=
    nat_lcm_residueDegree_dvd_normDownRamificationStep
      (K := K) (L := L') (L' := L) (M := M)
  have hstep :
      normDownRamificationStepNat (K := K) (L := L') (M := M) =
        Module.finrank K M := by
    change
      galoisNormDownRamificationStepNat (K := K) (L := L') (M := M) =
        Module.finrank K M
    exact galoisNormDownRamificationStepNat_eq_finrank
      (K := K) (L := L') (M := M)
  simpa [hstep] using hdiv

end CanonicalGaloisInvariantsSymm

end NAField

end TameAbhyankar

end
