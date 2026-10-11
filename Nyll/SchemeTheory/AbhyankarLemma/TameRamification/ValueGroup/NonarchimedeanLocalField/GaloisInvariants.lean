/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Invariants

/-!
# Galois valued-extension invariant bridges

This file records the field-degree identities for finite Galois extensions
whose canonical valuations form an extension. These identities keep the later
ramification-image comparison tied to the actual ramification index and
residue-field degree instead of assuming a separate endpoint comparison.
-/

noncomputable section

universe u

namespace TameAbhyankar

open scoped ValuativeRel

namespace NAField

section GaloisData

variable {K L M : Type u}
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
variable [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L]
variable [IsNonarchimedeanLocalField L]
variable [Field M]
variable [Algebra K L] [Algebra L M] [Algebra K M]
variable [IsScalarTower K L M]
variable [FiniteDimensional K L] [FiniteDimensional L M]
variable [IsGalois K L]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]

/-- The explicit norm-down step built from Galois valuation data: the Galois
residue degree of `L/K`, then the upper field degree `[M : L]`, then the
Galois ramification index of `L/K`. -/
def galoisNormDownRamificationStepNat : ℕ :=
  Module.finrank 𝓀[K] 𝓀[L] *
    (Module.finrank L M *
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K])

/-- The explicit Galois norm-down ramification step is the whole top field
degree `[M : K]`. -/
theorem galoisNormDownRamificationStepNat_eq_finrank :
    galoisNormDownRamificationStepNat (K := K) (L := L) (M := M) =
      Module.finrank K M := by
  have hgal :=
    ramificationIndex_mul_residueDegree_eq_finrank (K := K) (L := L)
  calc
    galoisNormDownRamificationStepNat (K := K) (L := L) (M := M) =
        Module.finrank 𝓀[K] 𝓀[L] *
          (Module.finrank L M *
            (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K]) := rfl
    _ =
        ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] *
          Module.finrank 𝓀[K] 𝓀[L]) *
          Module.finrank L M := by
      ac_rfl
    _ = Module.finrank K L * Module.finrank L M := by
      rw [hgal]
    _ = Module.finrank K M :=
      Module.finrank_mul_finrank K L M

end GaloisData

end NAField

end TameAbhyankar

end
