/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Galois.NormDown

/-!
# Primitive divisors from Galois norm-down lcm sources

This file contains the arithmetic cancellation layer on top of
`NAField.GaloisNormDown`: once the norm-down construction has supplied an lcm
divisor, these lemmas extract the primitive residue-degree factor by cancelling
the visible lower residue degree.
-/

noncomputable section

universe u

namespace TameAbhyankar

open LocalFieldTheory.DiscreteValuationField
open scoped ValuativeRel

namespace NAField

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

/-- Cancelling the visible `f(K,L)` factor from the norm-down ramification
step, the primitive part of the other lower residue degree divides the
powered Galois ramification step. -/
theorem residueDegreePrimitive_dvd_finrank_mul_galoisRamificationIndex :
    Module.finrank 𝓀[K] 𝓀[L'] /
        Nat.gcd (Module.finrank 𝓀[K] 𝓀[L])
          (Module.finrank 𝓀[K] 𝓀[L']) ∣
      Module.finrank L M *
        Ideal.ramificationIdx (𝓂[L] : Ideal 𝒪[L]) 𝒪[K] := by
  have hdiv :
      Nat.lcm (Module.finrank 𝓀[K] 𝓀[L])
          (Module.finrank 𝓀[K] 𝓀[L']) ∣
        Module.finrank 𝓀[K] 𝓀[L] *
          (Module.finrank L M *
            Ideal.ramificationIdx (𝓂[L] : Ideal 𝒪[L]) 𝒪[K]) := by
    simpa [normDownRamificationStepNat] using
      nat_lcm_residueDegree_dvd_normDownRamificationStep
        (K := K) (L := L) (L' := L') (M := M)
  exact
    div_gcd_dvd_of_lcm_dvd_mul_left
      (a := Module.finrank 𝓀[K] 𝓀[L])
      (b := Module.finrank 𝓀[K] 𝓀[L'])
      (c := Module.finrank L M *
        Ideal.ramificationIdx (𝓂[L] : Ideal 𝒪[L]) 𝒪[K])
      (residueDegree_pos (K := K) (L := L)) hdiv

end CommonTop

section GaloisPrimitiveDivisors

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

/-- With both lower branches supplied by Neu1999 Galois valuation data, the
primitive residue-degree divisor is sourced entirely from Galois data. -/
theorem galoisResidueDegreePrimitive_dvd_finrank_mul_galoisRamificationIndex :
    Module.finrank 𝓀[K] 𝓀[L'] /
        Nat.gcd
          (Module.finrank 𝓀[K] 𝓀[L])
          (Module.finrank 𝓀[K] 𝓀[L']) ∣
      Module.finrank L M *
        Ideal.ramificationIdx (𝓂[L] : Ideal 𝒪[L]) 𝒪[K] := by
  have hresidueDegree_pos :
      0 < Module.finrank 𝓀[K] 𝓀[L] := by
    exact residueDegree_pos (K := K) (L := L)
  have hdiv :
      Nat.lcm
          (Module.finrank 𝓀[K] 𝓀[L])
          (Module.finrank 𝓀[K] 𝓀[L']) ∣
        Module.finrank 𝓀[K] 𝓀[L] *
          (Module.finrank L M *
            Ideal.ramificationIdx (𝓂[L] : Ideal 𝒪[L]) 𝒪[K]) := by
    simpa [galoisNormDownRamificationStepNat] using
      nat_lcm_galoisResidueDegree_dvd_galoisNormDownRamificationStep
        (K := K) (L := L) (L' := L') (M := M)
  exact
    div_gcd_dvd_of_lcm_dvd_mul_left
      (a := Module.finrank 𝓀[K] 𝓀[L])
      (b := Module.finrank 𝓀[K] 𝓀[L'])
      (c := Module.finrank L M *
        Ideal.ramificationIdx (𝓂[L] : Ideal 𝒪[L]) 𝒪[K])
      hresidueDegree_pos hdiv

/-- Symmetric Galois-data primitive divisor for the `L'` branch. -/
theorem galoisResidueDegreePrimitive_dvd_finrank_mul_galoisRamificationIndex_symm :
    Module.finrank 𝓀[K] 𝓀[L] /
        Nat.gcd
          (Module.finrank 𝓀[K] 𝓀[L'])
          (Module.finrank 𝓀[K] 𝓀[L]) ∣
      Module.finrank L' M *
        Ideal.ramificationIdx (𝓂[L'] : Ideal 𝒪[L']) 𝒪[K] := by
  simpa using
    galoisResidueDegreePrimitive_dvd_finrank_mul_galoisRamificationIndex
      (K := K) (L := L') (L' := L) (M := M)

end GaloisPrimitiveDivisors

section CommonTopSymm

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
variable [FiniteDimensional K L'] [IsGalois K L']
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L')]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]

/-- Symmetric branch form: applying the norm-down construction to the `L'`
branch gives the primitive residue-degree divisor for `L`. -/
theorem residueDegreePrimitive_dvd_finrank_mul_galoisRamificationIndex_symm :
    Module.finrank 𝓀[K] 𝓀[L] /
        Nat.gcd (Module.finrank 𝓀[K] 𝓀[L'])
          (Module.finrank 𝓀[K] 𝓀[L]) ∣
      Module.finrank L' M *
        Ideal.ramificationIdx (𝓂[L'] : Ideal 𝒪[L']) 𝒪[K] := by
  have hdiv :
      Nat.lcm (Module.finrank 𝓀[K] 𝓀[L'])
          (Module.finrank 𝓀[K] 𝓀[L]) ∣
        Module.finrank 𝓀[K] 𝓀[L'] *
          (Module.finrank L' M *
            Ideal.ramificationIdx (𝓂[L'] : Ideal 𝒪[L']) 𝒪[K]) := by
    simpa [normDownRamificationStepNat] using
      nat_lcm_residueDegree_dvd_normDownRamificationStep
        (K := K) (L := L') (L' := L) (M := M)
  exact
    div_gcd_dvd_of_lcm_dvd_mul_left
      (a := Module.finrank 𝓀[K] 𝓀[L'])
      (b := Module.finrank 𝓀[K] 𝓀[L])
      (c := Module.finrank L' M *
        Ideal.ramificationIdx (𝓂[L'] : Ideal 𝒪[L']) 𝒪[K])
      (residueDegree_pos (K := K) (L := L')) hdiv

end CommonTopSymm

end NAField

end TameAbhyankar

end
